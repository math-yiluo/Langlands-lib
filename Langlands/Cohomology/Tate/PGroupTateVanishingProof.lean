import Langlands.Cohomology.Tate.CohomologicalTrivialityStatement
import Langlands.Cohomology.Tate.TransferLawsProof
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Two consecutive vanishing degrees for a `p`-group

For a finite `p`-group, actual Tate cohomology vanishing in two consecutive
degrees vanishes in every degree.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

namespace PGroupVanishing

set_option backward.isDefEq.respectTransparency false

attribute [-instance] ULift.module

section General

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- Actual Tate cohomology of a representation of a trivial group vanishes. -/
lemma tate_isZero_of_subsingleton [Subsingleton G] (B : Rep.{u} R G) (n : ℤ) :
    IsZero (tateCohomology B n) := by
  have hepi : Epi (coinducedEmbedding B) := by
    rw [Rep.epi_iff_surjective]
    intro f
    refine ⟨f.1 1, Subtype.ext (funext fun x => ?_)⟩
    rw [Subsingleton.elim x 1]
    change B.ρ 1 (f.1 1) = f.1 1
    simp
  have : IsIso (coinducedEmbedding B) := isIso_of_mono_of_epi _
  exact (coinduced_tate_isZero B n).of_iso
    ((tateCohomologyFunctor n).mapIso (asIso (coinducedEmbedding B)))

/-- The group order kills actual Tate cohomology. -/
lemma card_smul_eq_zero (A : Rep.{u} R G) (n : ℤ) (x : tateCohomology A n) :
    Fintype.card G • x = 0 := by
  classical
  let _ : Fintype (⊥ : Subgroup G) := Fintype.ofFinite _
  let _ : Fintype (G ⧸ (⊥ : Subgroup G)) := Fintype.ofFinite _
  have hres : restriction ⊥ A n x = 0 :=
    (ModuleCat.isZero_iff_subsingleton.mp (tate_isZero_of_subsingleton _ n)).elim _ 0
  have h := corestriction_restriction (⊥ : Subgroup G) A n x
  rw [hres, map_zero, Subgroup.index_bot, Nat.card_eq_fintype_card] at h
  exact h.symm

end General

section FixedPoints

variable {R P : Type u} [CommRing R] [Group P] [Finite P] {p : ℕ} [Fact p.Prime]

/-- A nonzero vector of a `p`-group representation killed by `p` generates a nonzero fixed
vector. -/
lemma exists_fixed_ne_zero (hP : IsPGroup p P) {M : Type u} [AddCommGroup M] [Module R M]
    (ρ : Representation R P M) (hM : ∀ m : M, p • m = 0) {a : M} (ha : a ≠ 0) :
    ∃ b ∈ AddSubgroup.closure (Set.range fun g : P => ρ g a), b ≠ 0 ∧ ∀ g : P, ρ g b = b := by
  set S : Set M := Set.range fun g : P => ρ g a with hS
  set V := AddSubgroup.closure S with hV
  have hmem : ∀ (g : P) (v : M), v ∈ V → ρ g v ∈ V := by
    intro g v hv
    have hle : AddSubgroup.map (ρ g).toAddMonoidHom V ≤ V := by
      rw [hV, AddMonoidHom.map_closure]
      apply AddSubgroup.closure_mono
      rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
      exact ⟨g * h, by simp [map_mul]⟩
    exact hle ⟨v, hv, rfl⟩
  have hfin : Finite V := by
    have : Finite S := Set.finite_range _
    refine AddCommGroup.finite_of_fg_isAddTorsion V fun v => ?_
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      ⟨p, (Fact.out : p.Prime).pos, Subtype.ext (hM v)⟩
  let _ : MulAction P V :=
    { smul := fun g v => ⟨ρ g v, hmem g v v.2⟩
      one_smul := fun v => Subtype.ext (by change ρ 1 v = v; simp)
      mul_smul := fun g h v => Subtype.ext (by
        change ρ (g * h) v = ρ g (ρ h v)
        simp [map_mul]) }
  have ha' : a ∈ V := AddSubgroup.subset_closure ⟨1, by simp⟩
  have hdvd : p ∣ Nat.card V := by
    have hord : addOrderOf (⟨a, ha'⟩ : V) = p := by
      apply addOrderOf_eq_prime
      · exact Subtype.ext (hM a)
      · intro h
        exact ha (congrArg Subtype.val h)
    rw [← hord]
    exact addOrderOf_dvd_natCard _
  have h0 : (0 : V) ∈ MulAction.fixedPoints P V := fun g =>
    Subtype.ext (by change ρ g 0 = 0; simp)
  obtain ⟨b, hb, hne⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hdvd h0
  exact ⟨b.1, b.2, fun h => hne (Subtype.ext h.symm), fun g => congrArg Subtype.val (hb g)⟩

end FixedPoints


section Killed

variable {R G : Type u} [CommRing R] [Group G]

lemma killed_apply {A : Rep.{u} R G} {n : ℕ} (h : n • 𝟙 A = 0) (a : A) : n • a = 0 := by
  have := congrArg (fun f : A ⟶ A => f.hom a) h
  exact this

lemma killed_of_apply {A : Rep.{u} R G} {n : ℕ} (h : ∀ a : A, n • a = 0) : n • 𝟙 A = 0 := by
  apply Rep.hom_ext
  ext a
  exact h a

lemma killed_coinduced {A : Rep.{u} R G} {n : ℕ} (h : n • 𝟙 A = 0) :
    n • 𝟙 (coinduced A) = 0 := by
  refine killed_of_apply fun v => Subtype.ext (funext fun x => ?_)
  exact killed_apply h (v.1 x)

lemma killed_cokernel {X Y : Rep.{u} R G} (f : X ⟶ Y) {n : ℕ} (h : n • 𝟙 Y = 0) :
    n • 𝟙 (cokernel f) = 0 := by
  rw [← cancel_epi (cokernel.π f), Preadditive.comp_nsmul, Category.comp_id, comp_zero]
  calc n • cokernel.π f = (n • 𝟙 Y) ≫ cokernel.π f := by
        rw [Preadditive.nsmul_comp, Category.id_comp]
    _ = 0 := by rw [h, zero_comp]

lemma killed_kernel {X Y : Rep.{u} R G} (f : X ⟶ Y) {n : ℕ} (h : n • 𝟙 X = 0) :
    n • 𝟙 (kernel f) = 0 := by
  rw [← cancel_mono (kernel.ι f), Preadditive.nsmul_comp, Category.id_comp, zero_comp]
  calc n • kernel.ι f = kernel.ι f ≫ (n • 𝟙 X) := by
        rw [Preadditive.comp_nsmul, Category.comp_id]
    _ = 0 := by rw [h, comp_zero]

end Killed

section Retraction

variable {p : ℕ} [Fact p.Prime]

/-- An `𝔽_p`-vector space retracts additively onto any additive subgroup. -/
lemma exists_retraction_zmod {M : Type u} [AddCommGroup M] [Module (ZMod p) M]
    (S : AddSubgroup M) : ∃ π : M →+ M, (∀ m, π m ∈ S) ∧ ∀ m ∈ S, π m = m := by
  obtain ⟨W', hW⟩ := Submodule.exists_isCompl (AddSubgroup.toZModSubmodule p S)
  refine ⟨((AddSubgroup.toZModSubmodule p S).subtype ∘ₗ
      (AddSubgroup.toZModSubmodule p S).projectionOnto W' hW).toAddMonoidHom,
    fun m => ((AddSubgroup.toZModSubmodule p S).projectionOnto W' hW m).2, fun m hm => ?_⟩
  exact congrArg Subtype.val (Submodule.projectionOnto_apply_left hW ⟨m, hm⟩)

/-- An additive group killed by a prime `p` retracts additively onto any subgroup. -/
lemma exists_retraction {M : Type u} [AddCommGroup M] (hM : ∀ m : M, p • m = 0)
    (S : AddSubgroup M) : ∃ π : M →+ M, (∀ m, π m ∈ S) ∧ ∀ m ∈ S, π m = m := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let _ : Module (ZMod p) M := AddCommGroup.zmodModule hM
  exact exists_retraction_zmod (p := p) S

end Retraction

section Elementary

variable {P : Type u} [Group P]

/-- An additive map between integral modules, as a scalar-linear map. -/
def integralLinear {M N : Type u} [AddCommGroup M] [Module IntegralScalar.{u} M]
    [AddCommGroup N] [Module IntegralScalar.{u} N] (f : M →+ N) :
    M →ₗ[IntegralScalar.{u}] N where
  toFun := f
  map_add' := f.map_add
  map_smul' r m := map_intCast_smul f IntegralScalar.{u} IntegralScalar.{u} r.down m

/-- The comparison map from an integral representation to the functions with values in its
invariants, determined by a linear map onto the invariants. -/
def toCoinduced (A : Rep.{u} IntegralScalar.{u} P)
    (π : A →ₗ[IntegralScalar.{u}] A.ρ.invariants) :
    A ⟶ coinduced (Rep.trivial IntegralScalar.{u} P A.ρ.invariants) :=
  Rep.resCoindToHom (⊥ : Subgroup P).subtype A
    (Rep.res (⊥ : Subgroup P).subtype (Rep.trivial IntegralScalar.{u} P A.ρ.invariants))
    (Rep.ofHom ⟨π, fun g => by
      have hg : (g : P) = 1 := Subgroup.mem_bot.mp g.2
      apply LinearMap.ext
      intro a
      change π (A.ρ (g : P) a) = π a
      rw [hg, map_one, Module.End.one_apply]⟩)

lemma toCoinduced_apply (A : Rep.{u} IntegralScalar.{u} P)
    (π : A →ₗ[IntegralScalar.{u}] A.ρ.invariants) (a : A) (x : P) :
    ((toCoinduced A π).hom a).1 x = π (A.ρ x a) := rfl

variable [Finite P] {p : ℕ} [Fact p.Prime]

lemma toCoinduced_injective (hP : IsPGroup p P) (A : Rep.{u} IntegralScalar.{u} P)
    (hA : ∀ a : A, p • a = 0) (π : A →ₗ[IntegralScalar.{u}] A.ρ.invariants)
    (hπ : ∀ (a : A) (ha : a ∈ A.ρ.invariants), π a = ⟨a, ha⟩) :
    Function.Injective (toCoinduced A π).hom := by
  intro a₁ a₂ h12
  rw [← sub_eq_zero]
  by_contra hne
  obtain ⟨b, hb, hb0, hbfix⟩ := exists_fixed_ne_zero hP A.ρ hA hne
  have hle : AddSubgroup.closure (Set.range fun g : P => A.ρ g (a₁ - a₂)) ≤
      (LinearMap.ker (toCoinduced A π).hom.toLinearMap).toAddSubgroup := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    change (toCoinduced A π).hom (A.ρ g (a₁ - a₂)) = 0
    rw [Rep.hom_comm_apply, map_sub, h12, sub_self, map_zero]
  have hbK : (toCoinduced A π).hom b = 0 := hle hb
  have h : (((toCoinduced A π).hom b).1 1 : A) = 0 := by
    rw [hbK]
    rfl
  rw [toCoinduced_apply, map_one, Module.End.one_apply, hπ b hbfix] at h
  exact hb0 h

/-- If `Φ` is not surjective onto a representation killed by `p`, some vector outside the image
is fixed modulo the image. -/
lemma exists_fixed_mod_range (hP : IsPGroup p P) {A C : Rep.{u} IntegralScalar.{u} P}
    (Φ : A ⟶ C) (hC : ∀ v : C, p • v = 0) {f : C} (hf : f ∉ Set.range Φ.hom) :
    ∃ f' : C, f' ∉ Set.range Φ.hom ∧ ∀ g : P, ∃ c : A, Φ.hom c = C.ρ g f' - f' := by
  let V : Submodule IntegralScalar.{u} C := LinearMap.range Φ.hom.toLinearMap
  have hV : ∀ g, V ≤ V.comap (C.ρ g) := by
    rintro g _ ⟨a, rfl⟩
    exact ⟨A.ρ g a, Rep.hom_comm_apply Φ g a⟩
  let ρQ : Representation IntegralScalar.{u} P (C ⧸ V) := C.ρ.quotient V hV
  have hQ : ∀ m : C ⧸ V, p • m = 0 := by
    intro m
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective V m
    rw [← Submodule.mkQ_apply, ← map_nsmul, hC v, map_zero]
  have hmem : ∀ v : C, (Submodule.Quotient.mk v : C ⧸ V) = 0 → v ∈ Set.range Φ.hom := by
    intro v h0
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp ((Submodule.Quotient.mk_eq_zero (p := V)).mp h0)
    exact ⟨a, ha⟩
  have hf0 : (Submodule.Quotient.mk f : C ⧸ V) ≠ 0 := fun h0 => hf (hmem f h0)
  obtain ⟨b, -, hb0, hbfix⟩ := exists_fixed_ne_zero hP ρQ hQ hf0
  obtain ⟨f', rfl⟩ := Submodule.Quotient.mk_surjective V b
  refine ⟨f', fun hf' => hb0 ?_, fun g => ?_⟩
  · obtain ⟨a, ha⟩ := hf'
    exact (Submodule.Quotient.mk_eq_zero (p := V)).mpr (LinearMap.mem_range.mpr ⟨a, ha⟩)
  · have h := hbfix g
    rw [Representation.quotient_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at h
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp h
    exact ⟨c, hc⟩

/-- An injective morphism into a representation killed by `p` whose fixed vectors lie in its
image is surjective, provided the source has vanishing first cohomology. -/
lemma surjective_of_fixed_mem_range (hP : IsPGroup p P) {A C : Rep.{u} IntegralScalar.{u} P}
    (Φ : A ⟶ C) (hinj : Function.Injective Φ.hom) (hC : ∀ v : C, p • v = 0)
    (h1 : IsZero (groupCohomology A 1))
    (hfixed : ∀ v : C, (∀ g : P, C.ρ g v = v) → v ∈ Set.range Φ.hom) :
    Function.Surjective Φ.hom := by
  intro f
  by_contra hf
  obtain ⟨f', hf', hc⟩ := exists_fixed_mod_range hP Φ hC hf
  choose c hc using hc
  have hcoc : c ∈ groupCohomology.cocycles₁ A := by
    rw [groupCohomology.mem_cocycles₁_iff]
    intro g h
    apply hinj
    rw [map_add, Rep.hom_comm_apply, hc, hc, hc, map_sub, map_mul, Module.End.mul_apply]
    abel
  have hcob : c ∈ groupCohomology.coboundaries₁ A :=
    (groupCohomology.H1π_eq_zero_iff ⟨c, hcoc⟩).mp
      ((ModuleCat.isZero_iff_subsingleton.mp h1).elim _ _)
  obtain ⟨y, hy⟩ := hcob
  have hfix : ∀ g : P, C.ρ g (f' - Φ.hom y) = f' - Φ.hom y := by
    intro g
    have hyg : A.ρ g y - y = c g := by
      rw [← groupCohomology.d₀₁_hom_apply]
      exact congrFun hy g
    rw [map_sub, ← Rep.hom_comm_apply, sub_eq_sub_iff_sub_eq_sub, ← map_sub, hyg, hc]
  obtain ⟨β, hβ⟩ := hfixed _ hfix
  exact hf' ⟨y + β, by rw [map_add, hβ, add_sub_cancel]⟩

lemma toCoinduced_surjective (hP : IsPGroup p P) (A : Rep.{u} IntegralScalar.{u} P)
    (hA : ∀ a : A, p • a = 0) (h1 : IsZero (groupCohomology A 1))
    (π : A →ₗ[IntegralScalar.{u}] A.ρ.invariants)
    (hπ : ∀ (a : A) (ha : a ∈ A.ρ.invariants), π a = ⟨a, ha⟩) :
    Function.Surjective (toCoinduced A π).hom := by
  refine surjective_of_fixed_mem_range hP (toCoinduced A π) (toCoinduced_injective hP A hA π hπ)
    (fun v => Subtype.ext (funext fun x => Subtype.ext (hA (v.1 x : A)))) h1 fun v hv => ?_
  have hconst : ∀ x : P, v.1 x = v.1 1 := by
    intro x
    have h := congrArg (fun w : coinduced (Rep.trivial IntegralScalar.{u} P A.ρ.invariants) =>
      w.1 1) (hv x)
    change v.1 (1 * x) = v.1 1 at h
    rwa [one_mul] at h
  have hβ : ((v.1 1 : A.ρ.invariants) : A) ∈ A.ρ.invariants := (v.1 1).2
  refine ⟨(v.1 1 : A.ρ.invariants), Subtype.ext (funext fun x => ?_)⟩
  rw [toCoinduced_apply, hβ x, hπ _ hβ, hconst x]

variable [Fintype P]

/-- A representation killed by `p` with vanishing first cohomology is coinduced, hence
acyclic for actual Tate cohomology. -/
lemma tate_isZero_of_killed_of_H1 (hP : IsPGroup p P) (A : Rep.{u} IntegralScalar.{u} P)
    (hA : ∀ a : A, p • a = 0) (h1 : IsZero (groupCohomology A 1)) (n : ℤ) :
    IsZero (tateCohomology A n) := by
  obtain ⟨π₁, hπ₁S, hπ₁id⟩ := exists_retraction hA A.ρ.invariants.toAddSubgroup
  let π₀ : A →+ A.ρ.invariants :=
    { toFun := fun a => ⟨π₁ a, hπ₁S a⟩
      map_zero' := Subtype.ext (map_zero π₁)
      map_add' := fun a b => Subtype.ext (map_add π₁ a b) }
  let π := integralLinear π₀
  have hπ : ∀ (a : A) (ha : a ∈ A.ρ.invariants), π a = ⟨a, ha⟩ := fun a ha =>
    Subtype.ext (hπ₁id a ha)
  let Φ := toCoinduced A π
  have : Mono Φ := (Rep.mono_iff_injective Φ).mpr (toCoinduced_injective hP A hA π hπ)
  have : Epi Φ := (Rep.epi_iff_surjective Φ).mpr (toCoinduced_surjective hP A hA h1 π hπ)
  have : IsIso Φ := isIso_of_mono_of_epi Φ
  exact (coinduced_tate_isZero _ n).of_iso ((tateCohomologyFunctor n).mapIso (asIso Φ))

end Elementary

section Vanishing

variable {P : Type u} [Group P] [Fintype P] {p : ℕ} [Fact p.Prime]

/-- For a representation killed by `p`, one vanishing degree forces vanishing in every
degree. -/
lemma tate_isZero_of_killed (hP : IsPGroup p P) (q : ℤ) :
    ∀ A : Rep.{u} IntegralScalar.{u} P, p • 𝟙 A = 0 → IsZero (tateCohomology A q) →
      ∀ n : ℤ, IsZero (tateCohomology A n) := by
  refine Int.inductionOn' q 1 ?_ ?_ ?_
  · intro A hA h n
    exact tate_isZero_of_killed_of_H1 hP A (killed_apply hA)
      (h.of_iso ((TateCohomology.isoGroupCohomology 1).app A).symm) n
  · intro k _ ih A hA h n
    have hS : IsZero (tateCohomology (shiftUp A) k) := h.of_iso (shiftUpIso A k)
    have h' := (ih (shiftUp A) (killed_cokernel _ (killed_coinduced hA)) hS (n - 1)).of_iso
      (shiftUpIso A (n - 1)).symm
    rwa [sub_add_cancel] at h'
  · intro k _ ih A hA h n
    have hS : IsZero (tateCohomology (shiftDown A) k) := by
      have h' := h.of_iso (shiftDownIso A (k - 1)).symm
      rwa [sub_add_cancel] at h'
    exact (ih (shiftDown A) (killed_kernel _ (killed_coinduced hA)) hS (n + 1)).of_iso
      (shiftDownIso A n)

/-- For a representation on which multiplication by `p` is injective, two consecutive vanishing
degrees force vanishing in every degree. -/
lemma tate_isZero_of_torsionFree (hP : IsPGroup p P) (A : Rep.{u} IntegralScalar.{u} P)
    (hA : Mono (p • 𝟙 A)) (q : ℤ) (h₀ : IsZero (tateCohomology A q))
    (h₁ : IsZero (tateCohomology A (q + 1))) (n : ℤ) : IsZero (tateCohomology A n) := by
  let S := ShortComplex.mk (p • 𝟙 A) (cokernel.π (p • 𝟙 A)) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have hQk : p • 𝟙 (cokernel (p • 𝟙 A)) = 0 := by
    rw [← cancel_epi (cokernel.π (p • 𝟙 A)), Preadditive.comp_nsmul, Category.comp_id,
      comp_zero, ← cokernel.condition (p • 𝟙 A), Preadditive.nsmul_comp, Category.id_comp]
  have hQ := tate_isZero_of_killed hP q _ hQk
    ((TateCohomology.exact₃ hS q).isZero_X₂ (h₀.eq_of_src _ _) (h₁.eq_of_tgt _ _))
  have hinj : ∀ (m : ℤ) (x : tateCohomology A (m + 1)), p • x = 0 → x = 0 := by
    intro m x hx
    have hmono : Mono ((tateCohomologyFunctor (m + 1)).map S.f) :=
      (TateCohomology.exact₁ hS m).mono_g ((hQ m).eq_of_src _ _)
    have : (tateCohomologyFunctor (R := IntegralScalar.{u}) (G := P) (m + 1)).Additive :=
      inferInstanceAs (tateComplexFunctor IntegralScalar.{u} P ⋙
        HomologicalComplex.homologyFunctor _ _ (m + 1)).Additive
    have hmap : (tateCohomologyFunctor (m + 1)).map S.f = p • 𝟙 _ := by
      change (tateCohomologyFunctor (m + 1)).map (p • 𝟙 A) = _
      rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
    rw [hmap, ModuleCat.mono_iff_injective] at hmono
    apply hmono
    rw [map_zero]
    exact hx
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hP
  have hall : ∀ m : ℤ, IsZero (tateCohomology A (m + 1)) := by
    intro m
    have key : ∀ (k : ℕ) (x : tateCohomology A (m + 1)), p ^ k • x = 0 → x = 0 := by
      intro k
      induction k with
      | zero =>
        intro x hx
        simpa using hx
      | succ k ih =>
        intro x hx
        apply ih
        apply hinj m
        rw [smul_smul, ← pow_succ']
        exact hx
    have h0 : ∀ x : tateCohomology A (m + 1), x = 0 := fun x =>
      key e x (by rw [← he, Nat.card_eq_fintype_card]; exact card_smul_eq_zero A (m + 1) x)
    exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun x y => (h0 x).trans (h0 y).symm⟩
  have h' := hall (n - 1)
  rwa [sub_add_cancel] at h'

/-- Two consecutive vanishing degrees propagate along a surjection from an acyclic
representation on which multiplication by `p` is injective. -/
lemma tate_isZero_of_cover (hP : IsPGroup p P) {L C : Rep.{u} IntegralScalar.{u} P}
    (ε : L ⟶ C) (hε : Epi ε) (hL : Mono (p • 𝟙 L))
    (hLz : ∀ n : ℤ, IsZero (tateCohomology L n)) (q : ℤ)
    (h₀ : IsZero (tateCohomology C q)) (h₁ : IsZero (tateCohomology C (q + 1))) (n : ℤ) :
    IsZero (tateCohomology C n) := by
  let S := ShortComplex.mk (kernel.ι ε) ε (kernel.condition ε)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel ε }
  let δ : ∀ m : ℤ, tateCohomology C m ≅ tateCohomology (kernel ε) (m + 1) := fun m =>
    have := tate_delta_isIso hS m (hLz m) (hLz (m + 1))
    asIso (TateCohomology.δ hS m)
  have hK : Mono (p • 𝟙 (kernel ε)) := by
    have hcomm : (p • 𝟙 (kernel ε)) ≫ kernel.ι ε = kernel.ι ε ≫ (p • 𝟙 L) := by
      rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]
    have : Mono ((p • 𝟙 (kernel ε)) ≫ kernel.ι ε) := by
      rw [hcomm]
      exact mono_comp _ _
    exact mono_of_mono _ (kernel.ι ε)
  have hK0 := tate_isZero_of_torsionFree hP (kernel ε) hK (q + 1)
    (h₀.of_iso (δ q).symm) (h₁.of_iso (δ (q + 1)).symm)
  exact (hK0 (n + 1)).of_iso (δ n)

end Vanishing

section Cover

variable {R G : Type u} [CommRing R] [Group G]

lemma mono_nsmul_coinduced {A : Rep.{u} R G} {n : ℕ} (h : Mono (n • 𝟙 A)) :
    Mono (n • 𝟙 (coinduced A)) := by
  rw [Rep.mono_iff_injective] at h ⊢
  intro v w hvw
  refine Subtype.ext (funext fun x => h ?_)
  exact congrArg (fun u : coinduced A => u.1 x) hvw

lemma mono_nsmul_trivial {X : Type u} [AddCommGroup X] [Module R X] [IsAddTorsionFree X]
    {n : ℕ} (hn : n ≠ 0) : Mono (n • 𝟙 (Rep.trivial R G X)) := by
  rw [Rep.mono_iff_injective]
  intro _ _ h
  exact nsmul_right_injective hn h

lemma integralScalar_isAddTorsionFree : IsAddTorsionFree IntegralScalar.{u} :=
  ⟨fun _ hn _ _ h => ULift.ext _ _ (nsmul_right_injective hn (congrArg ULift.down h))⟩

variable {P : Type u} [Group P] [Fintype P] {p : ℕ} [Fact p.Prime]

/-- Every integral representation is a quotient of an acyclic coinduced representation on
which multiplication by `p` is injective. -/
lemma exists_torsionFree_cover (C : Rep.{u} IntegralScalar.{u} P) :
    ∃ (L : Rep.{u} IntegralScalar.{u} P) (ε : L ⟶ C), Epi ε ∧ Mono (p • 𝟙 L) ∧
      ∀ n : ℤ, IsZero (tateCohomology L n) := by
  classical
  have := integralScalar_isAddTorsionFree.{u}
  let F := (C : Type u) →₀ IntegralScalar.{u}
  let T : Rep.{u} IntegralScalar.{u} P := Rep.trivial IntegralScalar.{u} P F
  let s : F →ₗ[IntegralScalar.{u}] C := Finsupp.linearCombination IntegralScalar.{u} id
  let sR : Rep.res (⊥ : Subgroup P).subtype T ⟶ Rep.res (⊥ : Subgroup P).subtype C :=
    Rep.ofHom ⟨s, fun g => by
      have hg : (g : P) = 1 := Subgroup.mem_bot.mp g.2
      apply LinearMap.ext
      intro a
      change s (T.ρ (g : P) a) = C.ρ (g : P) (s a)
      rw [hg, map_one, map_one, Module.End.one_apply, Module.End.one_apply]⟩
  refine ⟨coinduced T, Rep.coindMap (⊥ : Subgroup P).subtype sR ≫ coinducedProjection C,
    ?_, mono_nsmul_coinduced (mono_nsmul_trivial (Fact.out : p.Prime).ne_zero),
    coinduced_tate_isZero T⟩
  rw [Rep.epi_iff_surjective]
  intro c
  refine ⟨coinducedDelta T (Finsupp.single c 1), ?_⟩
  have hδ : (Rep.coindMap (⊥ : Subgroup P).subtype sR).hom
      (coinducedDelta T (Finsupp.single c 1)) = coinducedDelta C c := by
    apply Subtype.ext
    funext x
    change s ((coinducedDelta T (Finsupp.single c 1)).1 x) = (coinducedDelta C c).1 x
    rw [coinducedDelta_apply, coinducedDelta_apply]
    split_ifs
    · change Finsupp.linearCombination IntegralScalar.{u} id (Finsupp.single c 1) = c
      rw [Finsupp.linearCombination_single, one_smul]
      rfl
    · exact map_zero s
  change (coinducedProjection C).hom ((Rep.coindMap (⊥ : Subgroup P).subtype sR).hom
    (coinducedDelta T (Finsupp.single c 1))) = c
  rw [hδ, coinducedProjection_delta]

end Cover

end PGroupVanishing

open PGroupVanishing in
/-- Serre, *Local Fields*, IX §5, Theorem 8 for `p`-groups: two consecutive vanishing Tate
cohomology groups force vanishing in every degree. -/
theorem pGroupTateVanishing : PGroupTateVanishing.{u} := by
  intro p hp P _ _ hP C q h₀ h₁ n
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨L, ε, hε, hL, hLz⟩ := exists_torsionFree_cover (p := p) C
  exact tate_isZero_of_cover hP ε hε hL hLz q h₀ h₁ n

end Langlands.Tate
