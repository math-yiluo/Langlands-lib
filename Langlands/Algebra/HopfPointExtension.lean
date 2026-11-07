import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-! # Extending Hopf points of finite group algebras to Hopf points of lattices -/

noncomputable section

open TensorProduct Pointwise

namespace Langlands.Algebra.HopfPointExtension

section Defs

variable (R : Type*) [CommRing R] (C : Type*) [CommRing C] [Algebra R C]
  (M : Type*) [AddCommGroup M]

/-- The counit of the group algebra `C[M]`, as an `R`-algebra map. -/
def groupCounit : AddMonoidAlgebra C M →ₐ[R] C :=
  (AddMonoidAlgebra.lift C C M 1).restrictScalars R

/-- The diagonal map `C[M] → C[M × M]`, `X^χ ↦ X^(χ, χ)`. -/
def diagMap : AddMonoidAlgebra C M →ₐ[R] AddMonoidAlgebra C (M × M) :=
  AddMonoidAlgebra.mapDomainAlgHom R C ((AddMonoidHom.id M).prod (AddMonoidHom.id M))

/-- The first inclusion `C[M] → C[M × M]`. -/
def inlMap : AddMonoidAlgebra C M →ₐ[R] AddMonoidAlgebra C (M × M) :=
  AddMonoidAlgebra.mapDomainAlgHom R C (AddMonoidHom.inl M M)

/-- The second inclusion `C[M] → C[M × M]`. -/
def inrMap : AddMonoidAlgebra C M →ₐ[R] AddMonoidAlgebra C (M × M) :=
  AddMonoidAlgebra.mapDomainAlgHom R C (AddMonoidHom.inr M M)

variable {R C M}
variable {A : Type*} [CommRing A] [Bialgebra R A]

/-- The exterior product `A ⊗ A → C[M × M]` of an algebra map `A → C[M]` with itself. -/
def pairMap (f : A →ₐ[R] AddMonoidAlgebra C M) : A ⊗[R] A →ₐ[R] AddMonoidAlgebra C (M × M) :=
  Algebra.TensorProduct.lift ((inlMap R C M).comp f) ((inrMap R C M).comp f)
    (fun _ _ => Commute.all _ _)

/-- An algebra map from a bialgebra into a group algebra is a Hopf point when it
intertwines the comultiplications and the counits. These are the
`C`-points of the homomorphism functor from the diagonalizable group `D(M)` to
`Spec A`. -/
structure IsHopfPoint (f : A →ₐ[R] AddMonoidAlgebra C M) : Prop where
  comul : (pairMap f).comp (Bialgebra.comulAlgHom R A) = (diagMap R C M).comp f
  counit : (groupCounit R C M).comp f = (Algebra.ofId R C).comp (Bialgebra.counitAlgHom R A)

end Defs

section BoundedSums

variable {M : Type*} [AddCommGroup M]

/-- The set of sums of at most `N` elements of `s`. -/
def boundedSums (s : Set M) : ℕ → Set M
  | 0 => {0}
  | N + 1 => boundedSums s N ∪ (boundedSums s N + s)

theorem zero_mem_boundedSums (s : Set M) : ∀ N, (0 : M) ∈ boundedSums s N
  | 0 => rfl
  | N + 1 => Or.inl (zero_mem_boundedSums s N)

theorem boundedSums_mono (s : Set M) {N N' : ℕ} (h : N ≤ N') :
    boundedSums s N ⊆ boundedSums s N' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans Set.subset_union_left

theorem subset_boundedSums (s : Set M) {N : ℕ} (hN : 1 ≤ N) : s ⊆ boundedSums s N := by
  refine subset_trans ?_ (boundedSums_mono s hN)
  intro x hx
  exact Or.inr ⟨0, rfl, x, hx, zero_add x⟩

theorem boundedSums_add (s : Set M) (a : ℕ) : ∀ b,
    boundedSums s a + boundedSums s b ⊆ boundedSums s (a + b)
  | 0 => by
    rintro _ ⟨x, hx, y, rfl, rfl⟩
    simpa using hx
  | b + 1 => by
    rintro _ ⟨x, hx, y, hy | ⟨z, hz, w, hw, rfl⟩, rfl⟩
    · exact Or.inl (boundedSums_add s a b ⟨x, hx, y, hy, rfl⟩)
    · refine Or.inr ⟨x + z, boundedSums_add s a b ⟨x, hx, z, hz, rfl⟩, w, hw, ?_⟩
      exact add_assoc x z w

end BoundedSums

section Support

variable {R : Type*} [CommRing R] {C : Type*} [CommRing C] [Algebra R C]
  {M : Type*} [AddCommGroup M]

/-- The support of a product lies in the sum of the supports. -/
theorem support_mul_subset {x y : AddMonoidAlgebra C M} {s t : Set M}
    (hx : ↑x.coeff.support ⊆ s) (hy : ↑y.coeff.support ⊆ t) :
    ↑(x * y).coeff.support ⊆ s + t := by
  classical
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset x y hz)
  exact ⟨a, hx ha, b, hy hb, rfl⟩

/-- The support of a scalar is the origin. -/
theorem support_algebraMap_subset (a : R) :
    ↑(algebraMap R (AddMonoidAlgebra C M) a).coeff.support ⊆ ({0} : Set M) := by
  intro z hz
  rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply,
    AddMonoidAlgebra.coeff_single] at hz
  exact Set.mem_singleton_iff.mpr (Finset.mem_singleton.mp (Finsupp.support_single_subset hz))

/-- Powers of an element supported in `s` are supported in bounded sums. -/
theorem support_pow_subset {x : AddMonoidAlgebra C M} {s : Set M}
    (hx : ↑x.coeff.support ⊆ s) : ∀ k : ℕ, ↑(x ^ k).coeff.support ⊆ boundedSums s k
  | 0 => by
    rw [pow_zero]
    intro z hz
    exact Set.mem_singleton_iff.mpr (Finset.mem_singleton.mp
      (AddMonoidAlgebra.support_coeff_one_subset hz))
  | k + 1 => by
    rw [pow_succ]
    exact (support_mul_subset (support_pow_subset hx k) hx).trans Set.subset_union_right

/-- Supports of finite products of powers. -/
theorem support_prod_pow_subset {σ : Type*} (y : σ → AddMonoidAlgebra C M) {s : Set M}
    (hy : ∀ i, ↑(y i).coeff.support ⊆ s) (d : σ →₀ ℕ) :
    ↑(d.prod fun i e => y i ^ e).coeff.support ⊆ boundedSums s (d.sum fun _ e => e) := by
  classical
  unfold Finsupp.prod Finsupp.sum
  induction d.support using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    intro z hz
    exact Set.mem_singleton_iff.mpr (Finset.mem_singleton.mp
      (AddMonoidAlgebra.support_coeff_one_subset hz))
  | insert a t hat ih =>
    rw [Finset.prod_insert hat, Finset.sum_insert hat]
    refine (support_mul_subset (support_pow_subset (hy a) (d a)) ih).trans ?_
    exact boundedSums_add s (d a) _

/-- The image of a polynomial under an algebra map whose variables are supported
in `s` is supported in sums of at most `totalDegree` elements of `s`. -/
theorem support_aeval_subset {σ : Type*} (y : σ → AddMonoidAlgebra C M) {s : Set M}
    (hy : ∀ i, ↑(y i).coeff.support ⊆ s) (p : MvPolynomial σ R) :
    ↑(MvPolynomial.aeval y p).coeff.support ⊆ boundedSums s p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum, AddMonoidAlgebra.coeff_sum]
  intro z hz
  obtain ⟨d, hd, hz⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hz)
  rw [MvPolynomial.monomial_eq, map_mul, MvPolynomial.aeval_C, map_finsuppProd] at hz
  simp only [map_pow, MvPolynomial.aeval_X] at hz
  have h1 := support_mul_subset (support_algebraMap_subset (C := C) (M := M) (p.coeff d))
    (support_prod_pow_subset y hy d) hz
  simp only [Set.singleton_add, zero_add, Set.image_id'] at h1
  exact boundedSums_mono s (MvPolynomial.le_totalDegree hd) h1

end Support

section MapDomain

variable {R : Type*} [CommRing R] {C : Type*} [CommRing C] [Algebra R C]
  {M M' : Type*} [AddCommGroup M] [AddCommGroup M']

/-- Coefficientwise description of `mapDomain`. -/
theorem coeff_mapDomainAlgHom (π : M →+ M') (x : AddMonoidAlgebra C M) :
    (AddMonoidAlgebra.mapDomainAlgHom R C π x).coeff = Finsupp.mapDomain π x.coeff :=
  rfl

/-- `mapDomain` along a map injective on `S` is injective on elements supported in `S`. -/
theorem mapDomainAlgHom_injOn (π : M →+ M') {S : Set M} (hS : Set.InjOn π S)
    {x y : AddMonoidAlgebra C M} (hx : ↑x.coeff.support ⊆ S) (hy : ↑y.coeff.support ⊆ S)
    (h : AddMonoidAlgebra.mapDomainAlgHom R C π x = AddMonoidAlgebra.mapDomainAlgHom R C π y) :
    x = y := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.mapDomain_injOn S hS hx hy
  rw [← coeff_mapDomainAlgHom (R := R), ← coeff_mapDomainAlgHom (R := R), h]

/-- Supports of `mapDomain` images. -/
theorem support_mapDomainAlgHom_subset (π : M →+ M') {x : AddMonoidAlgebra C M} {S : Set M}
    (hx : ↑x.coeff.support ⊆ S) :
    ↑(AddMonoidAlgebra.mapDomainAlgHom R C π x).coeff.support ⊆ π '' S := by
  classical
  intro z hz
  rw [coeff_mapDomainAlgHom] at hz
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hz)
  exact ⟨a, hx ha, rfl⟩

/-- Lifting an element supported in `π '' s` to an element supported in `s`. -/
theorem exists_lift_of_support_subset (π : M →+ M') (s : Set M) (x : AddMonoidAlgebra C M')
    (hx : ↑x.coeff.support ⊆ π '' s) :
    ∃ y : AddMonoidAlgebra C M, ↑y.coeff.support ⊆ s ∧
      AddMonoidAlgebra.mapDomainAlgHom R C π y = x := by
  classical
  let ψ : M' → M := Function.invFunOn π s
  refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.mapDomain ψ x.coeff), ?_, ?_⟩
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hz)
    exact Function.invFunOn_mem (hx ha)
  · apply AddMonoidAlgebra.coeff_injective
    rw [coeff_mapDomainAlgHom, AddMonoidAlgebra.coeff_ofCoeff, ← Finsupp.mapDomain_comp]
    conv_rhs => rw [← Finsupp.mapDomain_id (v := x.coeff)]
    apply Finsupp.mapDomain_congr
    intro a ha
    exact Function.invFunOn_eq (hx ha)

theorem groupCounit_comp_mapDomain (π : M →+ M') :
    (groupCounit R C M').comp (AddMonoidAlgebra.mapDomainAlgHom R C π) = groupCounit R C M := by
  apply AlgHom.ext
  intro x
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m r =>
    simp [groupCounit, AddMonoidAlgebra.lift_single]

theorem mapDomain_comp_diagMap (π : M →+ M') :
    (AddMonoidAlgebra.mapDomainAlgHom R C (π.prodMap π)).comp (diagMap R C M) =
      (diagMap R C M').comp (AddMonoidAlgebra.mapDomainAlgHom R C π) := by
  rw [diagMap, diagMap, ← AddMonoidAlgebra.mapDomainAlgHom_comp,
    ← AddMonoidAlgebra.mapDomainAlgHom_comp]
  congr 1

theorem mapDomain_comp_inlMap (π : M →+ M') :
    (AddMonoidAlgebra.mapDomainAlgHom R C (π.prodMap π)).comp (inlMap R C M) =
      (inlMap R C M').comp (AddMonoidAlgebra.mapDomainAlgHom R C π) := by
  rw [inlMap, inlMap, ← AddMonoidAlgebra.mapDomainAlgHom_comp,
    ← AddMonoidAlgebra.mapDomainAlgHom_comp]
  congr 1
  ext <;> simp

theorem mapDomain_comp_inrMap (π : M →+ M') :
    (AddMonoidAlgebra.mapDomainAlgHom R C (π.prodMap π)).comp (inrMap R C M) =
      (inrMap R C M').comp (AddMonoidAlgebra.mapDomainAlgHom R C π) := by
  rw [inrMap, inrMap, ← AddMonoidAlgebra.mapDomainAlgHom_comp,
    ← AddMonoidAlgebra.mapDomainAlgHom_comp]
  congr 1
  ext <;> simp

variable {A : Type*} [CommRing A] [Bialgebra R A]

theorem mapDomain_comp_pairMap (π : M →+ M') (f : A →ₐ[R] AddMonoidAlgebra C M) :
    (AddMonoidAlgebra.mapDomainAlgHom R C (π.prodMap π)).comp (pairMap f) =
      pairMap ((AddMonoidAlgebra.mapDomainAlgHom R C π).comp f) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  simp only [pairMap, AlgHom.comp_apply, Algebra.TensorProduct.lift_tmul, map_mul]
  rw [← AlgHom.comp_apply _ (inlMap R C M), mapDomain_comp_inlMap,
    ← AlgHom.comp_apply _ (inrMap R C M), mapDomain_comp_inrMap]
  rfl

/-- Hopf points push forward along group homomorphisms. -/
theorem IsHopfPoint.mapDomain {f : A →ₐ[R] AddMonoidAlgebra C M} (hf : IsHopfPoint f)
    (π : M →+ M') : IsHopfPoint ((AddMonoidAlgebra.mapDomainAlgHom R C π).comp f) where
  comul := by
    rw [← mapDomain_comp_pairMap, AlgHom.comp_assoc, hf.comul, ← AlgHom.comp_assoc,
      mapDomain_comp_diagMap, AlgHom.comp_assoc]
  counit := by
    rw [← AlgHom.comp_assoc, groupCounit_comp_mapDomain, hf.counit]

end MapDomain

section Extension

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Bialgebra R A]
  {C : Type*} [CommRing C] [Algebra R C] {M M' : Type*} [AddCommGroup M] [AddCommGroup M']
  {σ : Type*}

/-- A family `gen` of algebra generators of a bialgebra `A` together with a degree
bound `N`: the relations among the generators are generated in total degree at most
`N`, and the comultiplication of each generator is a combination of tensors of
polynomials of degree at most `N` in the generators. -/
structure IsBoundedPresentation (gen : σ → A) (N : ℕ) : Prop where
  adjoin_eq_top : Algebra.adjoin R (Set.range gen) = ⊤
  ker_le : RingHom.ker (MvPolynomial.aeval (R := R) gen) ≤
    Ideal.span {p | MvPolynomial.aeval gen p = 0 ∧ p.totalDegree ≤ N}
  comul_mem : ∀ i, Bialgebra.comulAlgHom R A (gen i) ∈ Submodule.span R
    {x | ∃ p q : MvPolynomial σ R, p.totalDegree ≤ N ∧ q.totalDegree ≤ N ∧
      x = MvPolynomial.aeval gen p ⊗ₜ[R] MvPolynomial.aeval gen q}

/-- Uniqueness: Hopf points that are supported in `s` on generators and have the
same image modulo `π` are equal, when `π` is injective on `s`. -/
theorem eq_of_mapDomain_eq {gen : σ → A} (hgen : Algebra.adjoin R (Set.range gen) = ⊤)
    (π : M →+ M') {s : Set M} (hπ : Set.InjOn π s)
    {f f' : A →ₐ[R] AddMonoidAlgebra C M}
    (hf : ∀ i, ↑(f (gen i)).coeff.support ⊆ s) (hf' : ∀ i, ↑(f' (gen i)).coeff.support ⊆ s)
    (h : (AddMonoidAlgebra.mapDomainAlgHom R C π).comp f =
      (AddMonoidAlgebra.mapDomainAlgHom R C π).comp f') : f = f' := by
  apply AlgHom.ext_of_adjoin_eq_top hgen
  rintro _ ⟨i, rfl⟩
  exact mapDomainAlgHom_injOn (R := R) π hπ (hf i) (hf' i) (congrArg (fun F => F (gen i)) h)

theorem support_inlMap_mul_inrMap_subset {x y : AddMonoidAlgebra C M} {S : Set M}
    (hx : ↑x.coeff.support ⊆ S) (hy : ↑y.coeff.support ⊆ S) :
    ↑(inlMap R C M x * inrMap R C M y).coeff.support ⊆ S ×ˢ S := by
  have h1 := support_mapDomainAlgHom_subset (R := R) (AddMonoidHom.inl M M) hx
  have h2 := support_mapDomainAlgHom_subset (R := R) (AddMonoidHom.inr M M) hy
  refine (support_mul_subset h1 h2).trans ?_
  rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
  simpa using And.intro ha hb

/-- The extension lemma: if `π` is injective on sums of at most `N` elements of
`s`, then a Hopf point into `C[M']` whose values on the generators are supported
in `π '' s` is the image of a unique Hopf point into `C[M]` whose values on the
generators are supported in `s`. -/
theorem existsUnique_hopfPoint_extension {gen : σ → A} {N : ℕ}
    (hP : IsBoundedPresentation (R := R) gen N) (hN : 1 ≤ N)
    (π : M →+ M') {s : Set M} (hπ : Set.InjOn π (boundedSums s N))
    {g : A →ₐ[R] AddMonoidAlgebra C M'} (hg : IsHopfPoint g)
    (hgs : ∀ i, ↑(g (gen i)).coeff.support ⊆ π '' s) :
    ∃! f : A →ₐ[R] AddMonoidAlgebra C M, IsHopfPoint f ∧
      (∀ i, ↑(f (gen i)).coeff.support ⊆ s) ∧
      (AddMonoidAlgebra.mapDomainAlgHom R C π).comp f = g := by
  classical
  have hsN : s ⊆ boundedSums s N := subset_boundedSums s hN
  have hπs : Set.InjOn π s := hπ.mono hsN
  -- lifts of the values on generators
  choose y hys hyπ using fun i => exists_lift_of_support_subset (R := R) π s (g (gen i)) (hgs i)
  let φ : MvPolynomial σ R →ₐ[R] A := MvPolynomial.aeval gen
  have hφ : Function.Surjective φ := by
    intro a
    have ha : a ∈ φ.range := by
      rw [MvPolynomial.aeval_range, hP.adjoin_eq_top]; trivial
    obtain ⟨p, rfl⟩ := ha
    exact ⟨p, rfl⟩
  let F : MvPolynomial σ R →ₐ[R] AddMonoidAlgebra C M := MvPolynomial.aeval y
  have hF : (AddMonoidAlgebra.mapDomainAlgHom R C π).comp F = g.comp φ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, F, φ, MvPolynomial.aeval_X]
    exact hyπ i
  have hFs : ∀ p : MvPolynomial σ R, ↑(F p).coeff.support ⊆ boundedSums s p.totalDegree :=
    support_aeval_subset y hys
  have hker : ∀ p ∈ RingHom.ker φ, F p = 0 := by
    intro p hp
    have hp' := hP.ker_le hp
    refine Submodule.span_induction (p := fun p _ => F p = 0) ?_ ?_ ?_ ?_ hp'
    · rintro q ⟨hq, hdeg⟩
      apply mapDomainAlgHom_injOn (R := R) π hπ ((hFs q).trans (boundedSums_mono s hdeg))
        (by simp)
      rw [map_zero, ← AlgHom.comp_apply, hF, AlgHom.comp_apply]
      change g (φ q) = 0
      rw [hq, map_zero]
    · exact map_zero F
    · intro a b _ _ ha hb
      rw [map_add, ha, hb, add_zero]
    · intro a b _ hb
      rw [smul_eq_mul, map_mul, hb, mul_zero]
  let e := Ideal.quotientKerAlgEquivOfSurjective hφ
  let f : A →ₐ[R] AddMonoidAlgebra C M :=
    (Ideal.Quotient.liftₐ (RingHom.ker φ) F hker).comp e.symm.toAlgHom
  have hfφ : ∀ p, f (φ p) = F p := by
    intro p
    have : e.symm (φ p) = Ideal.Quotient.mk (RingHom.ker φ) p := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    show Ideal.Quotient.liftₐ (RingHom.ker φ) F hker (e.symm (φ p)) = F p
    rw [this]
    exact congrArg (fun G => G p) (Ideal.Quotient.liftₐ_comp (RingHom.ker φ) F hker)
  have hfgen : ∀ i, f (gen i) = y i := by
    intro i
    have := hfφ (MvPolynomial.X i)
    simpa [φ, F] using this
  have hfπ : (AddMonoidAlgebra.mapDomainAlgHom R C π).comp f = g := by
    apply AlgHom.ext
    intro a
    obtain ⟨p, rfl⟩ := hφ a
    rw [AlgHom.comp_apply, hfφ, ← AlgHom.comp_apply, hF, AlgHom.comp_apply]
  have hfs : ∀ i, ↑(f (gen i)).coeff.support ⊆ s := fun i => by rw [hfgen]; exact hys i
  refine ⟨f, ⟨?_, hfs, hfπ⟩, ?_⟩
  · refine ⟨?_, ?_⟩
    · -- comultiplication, checked on generators
      apply AlgHom.ext_of_adjoin_eq_top hP.adjoin_eq_top
      rintro _ ⟨i, rfl⟩
      have hπ2 : Set.InjOn (π.prodMap π) (boundedSums s N ×ˢ boundedSums s N) := by
        rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨a', b'⟩ ⟨ha', hb'⟩ h
        have h1 : π a = π a' := by simpa using congrArg Prod.fst h
        have h2 : π b = π b' := by simpa using congrArg Prod.snd h
        exact Prod.ext (hπ ha ha' h1) (hπ hb hb' h2)
      have hL : ↑((pairMap f).comp (Bialgebra.comulAlgHom R A) (gen i)).coeff.support ⊆
          boundedSums s N ×ˢ boundedSums s N := by
        rw [AlgHom.comp_apply]
        refine Submodule.span_induction
          (p := fun x _ => ↑(pairMap f x).coeff.support ⊆ boundedSums s N ×ˢ boundedSums s N)
          ?_ ?_ ?_ ?_ (hP.comul_mem i)
        · rintro _ ⟨p, q, hp, hq, rfl⟩
          simp only [pairMap, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply]
          erw [hfφ p, hfφ q]
          exact support_inlMap_mul_inrMap_subset ((hFs p).trans (boundedSums_mono s hp))
            ((hFs q).trans (boundedSums_mono s hq))
        · simp
        · intro a b _ _ ha hb
          rw [map_add, AddMonoidAlgebra.coeff_add]
          exact (Finset.coe_subset.mpr Finsupp.support_add).trans
            (by rw [Finset.coe_union]; exact Set.union_subset ha hb)
        · intro r a _ ha
          rw [map_smul, AddMonoidAlgebra.coeff_smul]
          exact (Finset.coe_subset.mpr Finsupp.support_smul).trans ha
      have hR : ↑((diagMap R C M).comp f (gen i)).coeff.support ⊆
          boundedSums s N ×ˢ boundedSums s N := by
        rw [AlgHom.comp_apply, diagMap]
        refine (support_mapDomainAlgHom_subset (R := R) _ (hfs i)).trans ?_
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨hsN ha, hsN ha⟩
      apply mapDomainAlgHom_injOn (R := R) (π.prodMap π) hπ2 hL hR
      rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← AlgHom.comp_assoc,
        mapDomain_comp_pairMap, hfπ, hg.comul, ← AlgHom.comp_assoc, mapDomain_comp_diagMap,
        AlgHom.comp_assoc, hfπ]
    · rw [← groupCounit_comp_mapDomain π, AlgHom.comp_assoc, hfπ, hg.counit]
  · rintro f' ⟨-, hf's, hf'π⟩
    exact eq_of_mapDomain_eq hP.adjoin_eq_top π hπs hf's hfs (hf'π.trans hfπ.symm)

end Extension

end Langlands.Algebra.HopfPointExtension
