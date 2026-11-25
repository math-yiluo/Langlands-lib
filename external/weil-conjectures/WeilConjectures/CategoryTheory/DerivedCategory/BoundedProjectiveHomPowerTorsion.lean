/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Power torsion of Hom from a bounded finite-projective complex

Source: Stacks Project, Tag 08EJ, affine paragraph.
(blueprint: lem-sc-bounded-projective-hom-power-torsion).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace DerivedCategory

private theorem projective_single_to_lower_eq_zero
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (F : C) [Projective F] (t : ℤ) (E : DerivedCategory C) [E.IsLE (t - 1)]
    (f : (singleFunctor C t).obj F ⟶ E) : f = 0 := by
  obtain ⟨K, hK, ⟨e⟩⟩ := exists_iso_Q_obj_of_isLE E (t - 1)
  have := hK
  have h : f ≫ e.hom = 0 :=
    from_singleFunctor_obj_eq_zero_of_projective (f ≫ e.hom) (t - 1) (by omega)
  simpa using (cancel_mono e.hom).1 (by simpa using h)

set_option backward.isDefEq.respectTransparency false in
private theorem projective_single_homology_injective
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (F : C) [Projective F] (t : ℤ) (E : DerivedCategory C) :
    Function.Injective (fun f : (singleFunctor C t).obj F ⟶ E ↦
      (homologyFunctor C t).map f) := by
  let ts := TStructure.t (C := C)
  let S := (singleFunctor C t).obj F
  let T := (ts.triangleLTGE t).obj E
  have hT := ts.triangleLTGE_distinguished t E
  have : ts.IsLE T.obj₁ (t - 1) := by
    change ts.IsLE ((ts.truncLT t).obj E) (t - 1)
    infer_instance
  have hv (f : S ⟶ T.obj₁) : f = 0 := projective_single_to_lower_eq_zero F t _ f
  have hpost : Function.Injective (fun f : S ⟶ E ↦ f ≫ T.mor₂) := by
    intro f g h
    obtain ⟨a, ha⟩ := T.coyoneda_exact₂ hT (f - g) (by simp [h])
    rw [hv a, Limits.zero_comp] at ha
    exact sub_eq_zero.mp ha
  let H := homologyFunctor C t
  have hH : Function.Injective (fun f : S ⟶ T.obj₃ ↦ H.map f) :=
    (homologyFunctor_map_bijective_of_isLE_of_isGE t).1
  intro f g h
  apply hpost
  apply hH
  simpa only [Functor.map_comp] using congrArg (fun a ↦ a ≫ H.map T.mor₂) h

set_option backward.isDefEq.respectTransparency false in
/-- Derived Hom from a projective module in degree t embeds linearly into module
Hom to cohomology in degree t. No finiteness or torsion assumption is used.
Source: Stacks Project, Tag 08EJ, affine single-term case.
(blueprint: lem-sc-bounded-projective-hom-power-torsion).

Proof: Maps from F[t] to objects concentrated below t vanish by projectivity.
Apply this to the first term of the canonical truncation triangle of M at t.
Exactness makes postcomposition with M -> truncGE(t,M) injective on maps from F[t].
Homology is injective on maps from F[t] to truncGE(t,M), by the shifted-heart
comparison. Consequently H^t is injective on maps from F[t] to M. Precompose
with H^t(F[t]) ≅ F to obtain the asserted map. It is additive; its A-linearity
follows from naturality of this comparison applied to scalar endomorphisms of F
and the A-linearity of the single functor. No linearity instance for the entire
homology functor is required. Zero F and the zero ring are included. -/
private theorem exists_projective_single_homology_embedding
    (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (F : ModuleCat.{u} A) (hp : Module.Projective A F) (t : ℤ)
    (M : DerivedCategory (ModuleCat.{u} A)) :
    ∃ e : (Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} A) t).obj F) ⟶ M) →ₗ[A]
      (F →ₗ[A] (homologyFunctor (ModuleCat.{u} A) t).obj M), Function.Injective e := by
  have : Module.Projective A F := hp
  have : CategoryTheory.Projective F := ModuleCat.projective_of_categoryTheory_projective F
  let H := homologyFunctor (ModuleCat.{u} A) t
  let S := (singleFunctor (ModuleCat.{u} A) t).obj F
  let ε := (singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) t).app F
  let e : (S ⟶ M) →ₗ[A] (F →ₗ[A] H.obj M) :=
    { toFun := fun α ↦ (ε.inv ≫ H.map α).hom
      map_add' := by intro α β; simp
      map_smul' := by
        intro c α
        have hs : c • α =
            (singleFunctor (ModuleCat.{u} A) t).map (c • 𝟙 F) ≫ α := by simp
        have hn : ε.inv ≫ H.map ((singleFunctor (ModuleCat.{u} A) t).map (c • 𝟙 F)) =
            (c • 𝟙 F) ≫ ε.inv :=
          ((singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) t).inv.naturality
            (c • 𝟙 F)).symm
        change (ε.inv ≫ H.map (c • α)).hom = c • (ε.inv ≫ H.map α).hom
        rw [hs, H.map_comp, ← Category.assoc, hn]
        simp }
  refine ⟨e, ?_⟩
  intro α β h
  apply projective_single_homology_injective F t M
  apply (cancel_epi ε.inv).1
  exact ModuleCat.hom_ext h

set_option backward.isDefEq.respectTransparency false in
/-- A complex supported in [a,b] is an extension of its stupid truncation below b
by its top term. The shorter complex's terms are old terms or zero objects.
Source: Stacks Project, Tag 08EJ, affine stupid-truncation triangle.
(blueprint: lem-sc-bounded-projective-hom-power-torsion).

Proof: The complex S consisting of P^b in degree b maps into P because P is
zero above b. Its map is an isomorphism in degree b and has zero source in other
degrees, so it is mono. Construct L as its cokernel complex. Evaluation preserves
cokernels, so L is zero in degree b and its terms are canonically isomorphic to
P's terms in every other degree. Thus L is supported in [a,b-1] and is the stupid
truncation below b. The sequence S -> P -> L is short exact; its derived triangle
is distinguished and supplies the three arrows.
This construction also works when b<a or the endpoint is zero; all the relevant
terms are then zero. No projectivity, finiteness, or torsion assumption is used. -/
private theorem exists_bounded_complex_top_triangle
    (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    (hb : ∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i)) :
    ∃ L : CochainComplex (ModuleCat.{u} A) ℤ,
      (∀ i : ℤ, i < a ∨ b - 1 < i → IsZero (L.X i)) ∧
      (∀ i : ℤ, Nonempty (L.X i ≅ P.X i) ∨ IsZero (L.X i)) ∧
      ∃ (ι : Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} A) b).obj (P.X b)) ⟶
          Q.obj P) (π : Q.obj P ⟶ Q.obj L)
        (δ : Q.obj L ⟶
          (Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} A) b).obj (P.X b)))⟦(1 : ℤ)⟧),
        Pretriangulated.Triangle.mk ι π δ ∈
          (Pretriangulated.distinguishedTriangles (C := DerivedCategory (ModuleCat.{u} A))) := by
  classical
  let S := (CochainComplex.singleFunctor (ModuleCat.{u} A) b).obj (P.X b)
  let ι : S ⟶ P := HomologicalComplex.mkHomFromSingle (𝟙 (P.X b)) (by
    intro i hi
    exact (hb i (Or.inr (by change b + 1 = i at hi; omega))).eq_of_tgt _ _)
  have hιb : IsIso (ι.f b) := by
    dsimp only [ι]
    rw [HomologicalComplex.mkHomFromSingle_f, Category.comp_id]
    infer_instance
  have hι : Mono ι := HomologicalComplex.mono_of_mono_f ι (fun i ↦ by
    by_cases hi : i = b
    · subst i
      infer_instance
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).mono _)
  let L := cokernel ι
  let sc := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
  have hsc : sc.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel sc (cokernelIsCokernel ι) }
  have eX (i : ℤ) : L.X i ≅ cokernel (ι.f i) :=
    PreservesCokernel.iso (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i) ι
  have hLb : IsZero (L.X b) := (isZero_cokernel_of_epi (ι.f b)).of_iso (eX b)
  have hLi (i : ℤ) (hi : i ≠ b) : Nonempty (L.X i ≅ P.X i) := by
    have hz : ι.f i = 0 :=
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_src _ _
    have hπ : IsIso (cokernel.π (ι.f i)) := by
      rw [hz]
      infer_instance
    exact ⟨eX i ≪≫ (asIso (cokernel.π (ι.f i))).symm⟩
  refine ⟨L, ?_, ?_, Q.map ι, Q.map (cokernel.π ι), triangleOfSESδ hsc,
    triangleOfSES_distinguished hsc⟩
  · intro i hi
    by_cases hib : i = b
    · subst i
      exact hLb
    · obtain ⟨e⟩ := hLi i hib
      exact (hb i (by omega)).of_iso e
  · intro i
    by_cases hi : i = b
    · subst i
      exact Or.inr hLb
    · exact Or.inl (hLi i hi)

private theorem finite_map_power_torsion
    (A : Type u) [CommRing A] {F N : Type u} [AddCommGroup F] [Module A F]
    [AddCommGroup N] [Module A N] [Module.Finite A F] (r : A)
    (hN : ∀ m : N, ∃ n : ℕ, r ^ n • m = 0) (f : F →ₗ[A] N) :
    ∃ n : ℕ, r ^ n • f = 0 := by
  classical
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := F)
  choose e he using fun i : Fin k ↦ hN (f (s i))
  let n := Finset.univ.sup e
  refine ⟨n, LinearMap.ext_on_range hs fun i ↦ ?_⟩
  have hi : e i ≤ n := Finset.le_sup (Finset.mem_univ i)
  change r ^ n • f (s i) = 0
  rw [← Nat.sub_add_cancel hi, pow_add, mul_smul, he i, smul_zero]

private theorem single_projective_power_torsion
    (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (r : A) (F : ModuleCat.{u} A) (hf : Module.Finite A F)
    (hp : Module.Projective A F) (t : ℤ) (M : DerivedCategory (ModuleCat.{u} A))
    (hM : ∀ m : (homologyFunctor (ModuleCat.{u} A) t).obj M,
      ∃ n : ℕ, r ^ n • m = 0)
    (α : Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} A) t).obj F) ⟶ M) :
    ∃ n : ℕ, r ^ n • α = 0 := by
  obtain ⟨e, he⟩ := exists_projective_single_homology_embedding A F hp t M
  have := hf
  obtain ⟨n, hn⟩ := finite_map_power_torsion A r hM (e α)
  exact ⟨n, he (by simpa using hn)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem interval_projective_power_torsion
    (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (r : A) (a : ℤ) (n : ℕ) (M : DerivedCategory (ModuleCat.{u} A))
    (hM : ∀ (i : ℤ) (m : (homologyFunctor (ModuleCat.{u} A) i).obj M),
      ∃ n : ℕ, r ^ n • m = 0)
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hb : ∀ i : ℤ, i < a ∨ a + n - 1 < i → IsZero (P.X i))
    (hf : ∀ i : ℤ, Module.Finite A (P.X i))
    (hp : ∀ i : ℤ, Module.Projective A (P.X i)) (α : Q.obj P ⟶ M) :
    ∃ k : ℕ, r ^ k • α = 0 := by
  induction n generalizing P with
  | zero =>
    have hz : IsZero P := (IsZero.iff_id_eq_zero _).2 (by
      apply HomologicalComplex.Hom.ext
      funext i
      exact (hb i (by omega)).eq_of_src _ _)
    have hq : IsZero (Q.obj P) := Functor.map_isZero Q hz
    exact ⟨0, by simpa using hq.eq_of_src α 0⟩
  | succ n ih =>
    obtain ⟨L, hL, hX, ι, π, δ, hT⟩ :=
      exists_bounded_complex_top_triangle A P a (a + n) (by
        intro i hi
        exact hb i (by omega))
    have hLf (i : ℤ) : Module.Finite A (L.X i) := by
      rcases hX i with ⟨⟨e⟩⟩ | hz
      · have := hf i
        exact Module.Finite.equiv e.toLinearEquiv.symm
      · have := ModuleCat.isZero_iff_subsingleton.1 hz
        infer_instance
    have hLp (i : ℤ) : Module.Projective A (L.X i) := by
      rcases hX i with ⟨⟨e⟩⟩ | hz
      · have := hp i
        exact Module.Projective.of_equiv e.toLinearEquiv.symm
      · have := ModuleCat.isZero_iff_subsingleton.1 hz
        infer_instance
    obtain ⟨k, hk⟩ := single_projective_power_torsion A r (P.X (a + n))
      (hf _) (hp _) (a + n) M (hM _) (ι ≫ α)
    change r ^ k • (ι ≫ α) = 0 at hk
    obtain ⟨β, hβ⟩ := Pretriangulated.Triangle.yoneda_exact₂ _ hT (r ^ k • α) (by
      change ι ≫ (r ^ k • α) = 0
      rw [Linear.comp_smul]
      exact hk)
    obtain ⟨l, hl⟩ := ih L hL hLf hLp β
    refine ⟨l + k, ?_⟩
    rw [pow_add, mul_smul, hβ, ← Linear.comp_smul, hl, comp_zero]

/-- Elementwise power torsion of all cohomology modules implies power torsion of
morphisms from a bounded complex of finite projective modules.
Source: Stacks Project, Tag 08EJ, affine paragraph.
(blueprint: lem-sc-bounded-projective-hom-power-torsion).

Proof: Induct on the length of a finite interval supporting P, simultaneously for
all targets with the displayed cohomological torsion property. The zero complex
has no nonzero morphisms. For a single projective term in degree t, projectivity
identifies derived Hom with module Hom into H^t(M). Choose a finite generating
set of that term. Each generator's image is killed by a power of r; the maximum
of these finitely many exponents kills the map by linearity. For more than one
term, the highest-degree term and the shorter stupid truncation give a distinguished
triangle. Restrict the given morphism to the highest-degree single term and kill it
by r^a using the single-term case. Exactness of contravariant Hom into M lifts
r^a times the morphism to the shorter truncation. Induction kills the lift by r^b.
Linearity of composition and r^(a+b) = r^b * r^a then kill the original morphism.
The argument uses no boundedness or finiteness hypothesis on M. Empty generating
sets, the zero ring and the zero complex all give zero Hom and exponent zero. -/
theorem bounded_projective_hom_power_torsion
    (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (r : A) (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hb : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i))
    (hf : ∀ i : ℤ, Module.Finite A (P.X i))
    (hp : ∀ i : ℤ, Module.Projective A (P.X i))
    (M : DerivedCategory (ModuleCat.{u} A))
    (hM : ∀ (i : ℤ) (m : (homologyFunctor (ModuleCat.{u} A) i).obj M),
      ∃ n : ℕ, r ^ n • m = 0)
    (α : Q.obj P ⟶ M) :
    ∃ n : ℕ, r ^ n • α = 0 := by
  obtain ⟨a, b, hb⟩ := hb
  let n := (b - a + 1).toNat
  apply interval_projective_power_torsion A r a n M hM P _ hf hp α
  intro i hi
  apply hb i
  dsimp [n] at hi
  omega

end DerivedCategory
