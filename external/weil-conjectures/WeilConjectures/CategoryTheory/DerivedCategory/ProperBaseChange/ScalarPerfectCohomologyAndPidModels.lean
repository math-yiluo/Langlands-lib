/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Triangulated.Generators
public import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Homology.Double
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.PerfectRingClassicalGenerator

/-! # Perfect scalar cohomology and finite-free models over a PID

Source: Stacks Project, more-algebra.tex, Tags 0657, 066Q and 0ATI; algebra.tex,
Tags 00IK and 00FP; Bhatt–Scholze, Proposition 6.8.11(3), scalar resolution paragraph
(blueprint: lem-weil-pbc-scalar-perfect-cohomology-and-pid-models).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- An injective finite-free presentation gives its two-term augmented model.
Source: Stacks Project, Tag 066Q, construction of a perfect module from a resolution;
Mathlib double-complex construction, as in `StandardQuotientsPerfect.twoTermResolution`
(blueprint: lem-weil-pbc-scalar-perfect-cohomology-and-pid-models). -/
private theorem twoTermResolution {R : Type u} [CommRing R]
    (s r : ℕ) (u : (Fin s → R) →ₗ[R] (Fin r → R)) (M : ModuleCat.{u} R)
    (q : ModuleCat.of R (Fin r → R) ⟶ M)
    (hw : ModuleCat.ofHom u ≫ q = 0)
    (hex : (ShortComplex.mk (ModuleCat.ofHom u) q hw).Exact)
    [Mono (ModuleCat.ofHom u)] [Epi q] :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ)
      (_hge : P.IsStrictlyGE (-1)) (_hle : P.IsStrictlyLE 0),
      (∀ i : ℤ, Module.Free R (P.X i) ∧ Module.Finite R (P.X i)) ∧
      ∃ (em : P.X (-1) ≅ ModuleCat.of R (Fin s → R))
        (e0 : P.X 0 ≅ ModuleCat.of R (Fin r → R)),
        P.d (-1) 0 = em.hom ≫ ModuleCat.ofHom u ≫ e0.inv ∧
        ∃ ε : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M,
          QuasiIso ε ∧
          ε.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom = e0.hom ≫ q ∧
          (∀ i : ℤ, i ≠ 0 → ε.f i = 0) := by
  classical
  let f : ModuleCat.of R (Fin s → R) ⟶ ModuleCat.of R (Fin r → R) := ModuleCat.ofHom u
  have hrel : (ComplexShape.up ℤ).Rel (-1) 0 := by simp
  let P : CochainComplex (ModuleCat.{u} R) ℤ := HomologicalComplex.double f hrel
  let em := HomologicalComplex.doubleXIso₀ f hrel
  let e0 := HomologicalComplex.doubleXIso₁ f hrel (by omega)
  have hz (i : ℤ) (hm : i ≠ -1) (h0 : i ≠ 0) : IsZero (P.X i) :=
    HomologicalComplex.isZero_double_X f hrel i hm h0
  have hge : P.IsStrictlyGE (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact hz i (by omega) (by omega)
  have hle : P.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact hz i (by omega) (by omega)
  have hterms (i : ℤ) : Module.Free R (P.X i) ∧ Module.Finite R (P.X i) := by
    by_cases hm : i = -1
    · subst i
      exact ⟨Module.Free.of_equiv em.toLinearEquiv.symm,
        Module.Finite.equiv em.toLinearEquiv.symm⟩
    · by_cases h0 : i = 0
      · subst i
        exact ⟨Module.Free.of_equiv e0.toLinearEquiv.symm,
          Module.Finite.equiv e0.toLinearEquiv.symm⟩
      · have : Subsingleton (P.X i) := ModuleCat.subsingleton_of_isZero (hz i hm h0)
        exact ⟨inferInstance, inferInstance⟩
  let L := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M
  let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0 M
  have hL (i : ℤ) (hi : i ≠ 0) : IsZero (L.X i) :=
    HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi
  let ε : P ⟶ L := HomologicalComplex.mkHomFromDouble hrel (by omega) 0 (q ≫ e.inv)
    (by change 0 ≫ L.d (-1) 0 = f ≫ q ≫ e.inv
        rw [zero_comp, ← Category.assoc, show f ≫ q = 0 from hw, zero_comp])
    (by intro i hi; exact (hL i (by simp only [ComplexShape.up_Rel] at hi; omega)).eq_of_tgt _ _)
  have hε0 : ε.f 0 ≫ e.hom = e0.hom ≫ q := by
    simp [ε, e0]
  have hεi (i : ℤ) (hi : i ≠ 0) : ε.f i = 0 := (hL i hi).eq_of_tgt _ _
  have hmono : Mono (P.d (-1) 0) := by
    dsimp [P]
    rw [HomologicalComplex.double_d f hrel (by omega)]
    infer_instance
  have hε : QuasiIso ε := by
    rw [quasiIso_iff]
    intro i
    by_cases hi : i = 0
    · subst i
      rw [quasiIsoAt_iff' ε (-1) 0 1 (by simp) (by simp)]
      apply (ShortComplex.quasiIso_iff_of_zeros' _
        ((hz 1 (by omega) (by omega)).eq_of_tgt _ _)
        ((hL (-1) (by omega)).eq_of_src _ _)
        ((hL 1 (by omega)).eq_of_tgt _ _)).2
      have heq : P.d (-1) 0 ≫ ε.f 0 = 0 := by
        rw [← ε.comm]
        simp [hεi (-1) (by omega)]
      let S := ShortComplex.mk (P.d (-1) 0) (ε.f 0) heq
      let T := ShortComplex.mk f q hw
      let iso : S ≅ T := ShortComplex.isoMk em e0 e
        (by dsimp [S, T, P, em, e0]; rw [HomologicalComplex.double_d f hrel (by omega)]; simp)
        hε0.symm
      have hs : S.Exact := (ShortComplex.exact_iff_of_iso iso).2 hex
      have : Epi (ε.f 0) := by
        have : Epi (ε.f 0 ≫ e.hom) := by rw [hε0]; infer_instance
        exact (epi_comp_iff_of_isIso (ε.f 0) e.hom).1 inferInstance
      exact ⟨hs, show Epi (ε.f 0) from inferInstance⟩
    · have hLex : L.ExactAt i := HomologicalComplex.ExactAt.of_isZero (hL i hi)
      rw [quasiIsoAt_iff_exactAt' ε i hLex]
      by_cases hm : i = -1
      · subst i
        rw [HomologicalComplex.exactAt_iff' P (-2) (-1) 0 (by simp) (by simp)]
        apply (ShortComplex.exact_iff_mono _ ((hz (-2) (by omega) (by omega)).eq_of_src _ _)).2
        exact hmono
      · exact HomologicalComplex.ExactAt.of_isZero (hz i hm hi)
  exact ⟨P, hge, hle, hterms, em, e0,
    HomologicalComplex.double_d f hrel (by omega), ε, hε, hε0, hεi⟩

/-- Perfect complexes over a Noetherian ring have finitely presented cohomology, vanishing
outside every bounded finite-projective model's term interval. Over a PID, every specified
finite-free surjection onto a finitely presented module extends to an augmented two-term
finite-free resolution in degrees `[-1, 0]`; the module in degree zero is perfect and belongs
to the thick subcategory generated by the ring in degree zero.

Source: Stacks Project, more-algebra.tex, Tags 0657, 066Q and 0ATI; algebra.tex,
Tags 00IK and 00FP; more-algebra.tex, Tag 0ASU; Bhatt–Scholze, Proposition 6.8.11(3)
(blueprint: lem-weil-pbc-scalar-perfect-cohomology-and-pid-models).

Proof plan:
1. By def-pc-perfect-ring-complex choose a bounded finite-projective representative C of P.
For every such representative supported in [a,b], def-weil-abstract-derived-category
identifies H^q(P) with ker(d^q)/im(d^(q-1)). Outside [a,b] its ambient term is zero,
so the cohomology vanishes. The same argument applies to every representative.
2. The cycles are finite by lem-weil-pbc-noetherian-submodule-finite, as submodules of the
finite terms. Their quotients are finite, hence finitely presented by
lem-sc-noetherian-finite-module-finite-presentation. Transport along the cohomology
isomorphism to obtain the assertion for P.
3. For the specified surjection v, apply lem-weil-pbc-pid-submodule-finite-basis to its
kernel in A^r, using the coordinate basis of A^r. A basis indexed by Fin s identifies
A^s with ker v. Compose that identification with the inclusion to obtain an injective u
whose range is exactly ker v. This retains v and does not assume N is torsion-free.
4. Form the complex F with u in degrees -1 and 0, zero elsewhere, and augment by v.
The relation v u = 0 makes this a chain map. Its cohomology in degree -1 is ker u = 0;
in degree 0 it is A^r/im u, mapped isomorphically onto N by surjectivity and exactness.
Every other cohomology object is zero. Thus the augmentation is a quasi-isomorphism.
5. The coordinate bases and the empty bases make every term finite free
(def-weil-pbc-free-module), hence projective by lem-weil-pbc-free-module-projective.
This bounded model proves perfectness by def-pc-perfect-ring-complex, including zero
modules and zero ranks.
6. Apply lem-sf-perfect-ring-classical-generator: perfect objects are exactly the thick
subcategory generated by A[0], with the thick closure of pur9-def-thick realized by
the singleton's triangEnvelope. -/
theorem scalar_perfect_cohomology_and_pid_models (A : Type u) [CommRing A]
    [IsNoetherianRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)] :
    (∀ (P : DerivedCategory (ModuleCat.{u} A)), IsPerfectRingComplex P →
      (∀ q : ℤ, Module.FinitePresentation A ((homologyFunctor (ModuleCat.{u} A) q).obj P)) ∧
      ∀ (C : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ),
        C.IsStrictlyGE a → C.IsStrictlyLE b →
        (∀ i : ℤ, Module.Projective A (C.X i) ∧ Module.Finite A (C.X i)) →
        Nonempty (P ≅ Q.obj C) →
        ∀ q : ℤ, q < a ∨ b < q →
          IsZero ((homologyFunctor (ModuleCat.{u} A) q).obj P)) ∧
    (∀ [IsDomain A] [IsPrincipalIdealRing A]
      (N : ModuleCat.{u} A) [Module.FinitePresentation A N]
      (r : ℕ) (v : (Fin r → A) →ₗ[A] N), Function.Surjective v →
      ∃ (s : ℕ) (u : (Fin s → A) →ₗ[A] (Fin r → A)),
        Function.Injective u ∧ LinearMap.range u = LinearMap.ker v ∧
        (∃ (F : CochainComplex (ModuleCat.{u} A) ℤ),
          F.IsStrictlyGE (-1) ∧ F.IsStrictlyLE 0 ∧
          ∃ (em : F.X (-1) ≅ ModuleCat.of A (Fin s → A))
            (e0 : F.X 0 ≅ ModuleCat.of A (Fin r → A)),
            F.d (-1) 0 = em.hom ≫ ModuleCat.ofHom u ≫ e0.inv ∧
            ∃ ε : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N,
              QuasiIso ε ∧
              ε.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).hom =
                e0.hom ≫ ModuleCat.ofHom v ∧
              (∀ i : ℤ, i ≠ 0 → ε.f i = 0)) ∧
        IsPerfectRingComplex ((singleFunctor (ModuleCat.{u} A) 0).obj N) ∧
        (ObjectProperty.singleton
          ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))).triangEnvelope
            ((singleFunctor (ModuleCat.{u} A) 0).obj N)) := by
  classical
  constructor
  · intro P hP
    constructor
    · obtain ⟨C, a, b, ha, hb, hterms, ⟨e⟩⟩ := hP
      intro q
      have : Module.Finite A (C.X q) := (hterms q).2
      let S := C.sc q
      have : Module.Finite A S.X₂ := (hterms q).2
      have : Module.Finite A (LinearMap.ker S.g.hom) :=
        Module.Finite.of_injective _ (LinearMap.ker S.g.hom).injective_subtype
      have : Module.Finite A
          (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) := inferInstance
      have : Module.Finite A S.moduleCatLeftHomologyData.H := by
        change Module.Finite A
          (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
        infer_instance
      have hfin : Module.Finite A (C.homology q) :=
        Module.Finite.equiv S.moduleCatHomologyIso.toLinearEquiv.symm
      let eH : (homologyFunctor (ModuleCat.{u} A) q).obj P ≅ C.homology q :=
        (homologyFunctor (ModuleCat.{u} A) q).mapIso e ≪≫
          (homologyFunctorFactors (ModuleCat.{u} A) q).app C
      have : Module.Finite A ((homologyFunctor (ModuleCat.{u} A) q).obj P) :=
        Module.Finite.equiv eH.toLinearEquiv.symm
      exact Module.finitePresentation_of_finite A _
    · intro C a b ha hb hterms he q hq
      obtain ⟨e⟩ := he
      let eH : (homologyFunctor (ModuleCat.{u} A) q).obj P ≅ C.homology q :=
        (homologyFunctor (ModuleCat.{u} A) q).mapIso e ≪≫
          (homologyFunctorFactors (ModuleCat.{u} A) q).app C
      apply IsZero.of_iso (Y := C.homology q) _ eH
      rcases hq with hq | hq
      · exact (HomologicalComplex.ExactAt.of_isZero
          (C.isZero_of_isStrictlyGE a q hq)).isZero_homology
      · exact (HomologicalComplex.ExactAt.of_isZero
          (C.isZero_of_isStrictlyLE b q hq)).isZero_homology
  · intro _ _ N _ r v hv
    obtain ⟨s, ⟨b⟩⟩ := (LinearMap.ker v).nonempty_basis_of_pid (Pi.basisFun A (Fin r))
    let h := b.equivFun.symm
    let u := (LinearMap.ker v).subtype.comp h.toLinearMap
    have hu : Function.Injective u := Subtype.val_injective.comp h.injective
    have hrange : LinearMap.range u = LinearMap.ker v := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact (h y).property
      · intro hx
        exact ⟨h.symm ⟨x, hx⟩, by simp [u]⟩
    let f : ModuleCat.of A (Fin s → A) ⟶ ModuleCat.of A (Fin r → A) := ModuleCat.ofHom u
    let q : ModuleCat.of A (Fin r → A) ⟶ N := ModuleCat.ofHom v
    have hw : f ≫ q = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change v (u x) = 0
      exact LinearMap.mem_ker.mp (hrange ▸ LinearMap.mem_range_self u x)
    have hex : (ShortComplex.mk f q hw).Exact := by
      rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
      exact hrange
    have : Mono f := (ModuleCat.mono_iff_injective f).2 hu
    have : Epi q := (ModuleCat.epi_iff_surjective q).2 hv
    obtain ⟨F, hge, hle, hterms, em, e0, hd, ε, hε, hε0, hεi⟩ :=
      twoTermResolution s r u N q hw hex
    have hperfect : IsPerfectRingComplex ((singleFunctor _ 0).obj N) := by
      have : QuasiIso ε := hε
      refine ⟨F, -1, 0, hge, hle, ?_, ⟨(asIso (Q.map ε)).symm⟩⟩
      intro i
      have : Module.Free A (F.X i) := (hterms i).1
      exact ⟨inferInstance, (hterms i).2⟩
    refine ⟨s, u, hu, hrange, ?_, hperfect, ?_⟩
    · exact ⟨F, hge, hle, em, e0, hd, ε, hε, hε0, hεi⟩
    · rw [← isPerfectRingComplex_eq_triangEnvelope_singleton A]
      exact hperfect

end DerivedCategory
