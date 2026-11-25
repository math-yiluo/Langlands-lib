/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalPerfectReductionHomML
import Mathlib.Algebra.Category.ModuleCat.Limits
import WeilConjectures.Algebra.Module.RationalPerfectPairing
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # The uniform torsion bound for an integral scalar endomorphism complex

Source: current blueprint, proposition-local-structure-integral-constructible-complexes, compatible
isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ZeroObject TensorProduct

namespace AlgebraicGeometry.ProEtale

private theorem finite_tensor_terms (B : Type u) [CommRing B]
    (E F : CochainComplex (ModuleCat.{u} B) ℤ)
    (bE bF : ℤ)
    (hEb : ∀ j : ℤ, bE < j → IsZero (E.X j))
    (hFb : ∀ j : ℤ, bF < j → IsZero (F.X j))
    (hE : ∀ j : ℤ, Module.Finite B (E.X j))
    (hF : ∀ j : ℤ, Module.Finite B (F.X j))
    (i : ℤ) :
    Module.Finite B ((CochainComplex.mapBifunctor E F
      (curriedTensor (ModuleCat B))).X i) := by
  classical
  let T := CochainComplex.mapBifunctor E F (curriedTensor (ModuleCat B))
  let I := {p : ℤ // p ∈ Finset.Icc (i - bF) bE}
  let G : I → ModuleCat B := fun p ↦ E.X p.val ⊗ F.X (i - p.val)
  let π : (∐ G) ⟶ T.X i := Sigma.desc (fun p ↦
    HomologicalComplex.ιMapBifunctor E F (curriedTensor _) (.up ℤ)
      p.val (i - p.val) i (by simp))
  have hπ : Epi π := by
    constructor
    intro Y g h hgh
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hpq' : p + q = i := hpq
    by_cases hp : p ∈ Finset.Icc (i - bF) bE
    · have he := congrArg ((Sigma.ι G ⟨p, hp⟩) ≫ ·) hgh
      have hq : q = i - p := by omega
      subst q
      simpa only [π, ← Category.assoc, Sigma.ι_comp_desc] using he
    · have hz : IsZero ((E.X p ⊗ F.X q) : ModuleCat B) := by
        by_cases hpe : bE < p
        · exact Functor.map_isZero (tensorRight (F.X q)) (hEb p hpe)
        · have hq : bF < q := by simp only [Finset.mem_Icc] at hp; omega
          exact Functor.map_isZero (tensorLeft (E.X p)) (hFb q hq)
      exact hz.eq_of_src _ _
  have hG (p : I) : Module.Finite B (G p) := by
    have := hE p.val
    have := hF (i - p.val)
    change Module.Finite B (E.X p.val ⊗[B] F.X (i - p.val))
    infer_instance
  have : ∀ p : I, Module.Finite B (G p) := hG
  let e : ModuleCat.of B (∀ p : I, G p) ≅ ∐ G :=
    (ModuleCat.biproductIsoPi G).symm ≪≫ biproduct.isoCoproduct G
  have : Module.Finite B ((∐ G) : ModuleCat B) := Module.Finite.of_surjective e.hom.hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  exact Module.Finite.of_surjective π.hom ((ModuleCat.epi_iff_surjective _).1 hπ)

private theorem finite_hom_term
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (P Q : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hp : ∀ i, Module.Finite A (P.X i)) (hq : ∀ i, Module.Finite A (Q.X i)) (q : ℤ) :
    Module.Finite A ((CochainComplex.moduleHomComplex P Q).X q) := by
  classical
  let φ : CochainComplex.HomComplex.Cochain P Q q →ₗ[A]
      (∀ i : Set.Icc a b, P.X i.val ⟶ Q.X (i.val + q)) :=
    { toFun := fun z i ↦ z.v i.val (i.val + q) rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hinj : Function.Injective φ := by
    intro z w h
    apply CochainComplex.HomComplex.Cochain.ext
    intro i j hij
    subst j
    by_cases hi : i ∈ Set.Icc a b
    · exact congrFun h ⟨i, hi⟩
    · have hz : IsZero (P.X i) := by
        by_cases hil : i < a
        · exact P.isZero_of_isStrictlyGE a i hil
        · exact P.isZero_of_isStrictlyLE b i (by simp only [Set.mem_Icc] at hi; omega)
      exact hz.eq_of_src _ _
  have hfin : ∀ i : Set.Icc a b, Module.Finite A (P.X i.val ⟶ Q.X (i.val + q)) := by
    intro i
    have := hp i.val
    have := hq (i.val + q)
    exact Module.Finite.equiv (ModuleCat.homLinearEquiv (S := A)).symm
  exact Module.Finite.of_injective φ hinj

private theorem finite_dual_tensor_homology
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hp : ∀ i, Module.Finite A (P.X i)) :
    Module.Finite A ((CochainComplex.mapBifunctor
      (CochainComplex.moduleHomComplex P
        ((CochainComplex.singleFunctor _ 0).obj (ModuleCat.of A A))) P
          (curriedTensor _)).homology 1) := by
  classical
  let Q := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  let D := CochainComplex.moduleHomComplex P Q
  have hQ (i : ℤ) : Module.Finite A (Q.X i) := by
    by_cases hi : i = 0
    · subst i
      exact Module.Finite.equiv
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).toLinearEquiv.symm
    · have hz : IsZero (Q.X i) :=
        HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of A A) i hi
      have : Subsingleton (Q.X i) := ModuleCat.isZero_iff_subsingleton.mp hz
      infer_instance
  have hD (i : ℤ) : Module.Finite A (D.X i) := finite_hom_term P Q a b ha hb hp hQ i
  have hDb (i : ℤ) (hi : -a < i) : IsZero (D.X i) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    constructor
    intro z w
    apply CochainComplex.HomComplex.Cochain.ext
    intro j k hjk
    by_cases hk : k = 0
    · subst k
      exact (P.isZero_of_isStrictlyGE a j (by omega)).eq_of_src _ _
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of A A) k hk).eq_of_tgt _ _
  let T := CochainComplex.mapBifunctor D P (curriedTensor _)
  have : Module.Finite A (T.X 1) := finite_tensor_terms A D P (-a) b
    hDb (fun i hi ↦ P.isZero_of_isStrictlyLE b i hi) hD hp 1
  let S := T.sc 1
  let : Module.Finite A S.X₂ := ‹Module.Finite A (T.X 1)›
  have : Module.Finite A (LinearMap.ker S.g.hom) :=
    Module.Finite.of_injective _ (LinearMap.ker S.g.hom).injective_subtype
  have : Module.Finite A S.moduleCatLeftHomologyData.H := by
    change Module.Finite A (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
    infer_instance
  exact Module.Finite.equiv S.moduleCatHomologyIso.toLinearEquiv.symm

/-- The torsion in degree one of the scalar dual-tensor complex is killed by one
uniformizer power.
Source: current blueprint proposition-local-structure-integral-constructible-complexes, compatible
isomorphisms, first paragraph (blueprint: lem-pe-integral-scalar-torsion-bound).

Proof: The scalar integer ring is a DVR, hence Noetherian. Each term of the dual
complex embeds into the finite product of the linear Hom modules indexed by the
bounded support of P. These modules are finite over the Noetherian ring. The dual
is bounded above by minus the lower bound of P. In each degree the tensor totalization
therefore has only finitely many nonzero summands, all finite. Its cycles and homology
are finite as well. In a Noetherian module the ascending chain of kernels of powers
of the uniformizer stabilizes. Every torsion element is killed by a power of the
uniformizer: factor a nonzero annihilator as a unit times such a power. The stabilized
kernel thus contains every torsion element. -/
theorem integralScalarDualTensor_torsionBound
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (a b : ℤ) (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hp : ∀ i, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i)) :
    ∃ e : ℕ, ∀ x : (internalPerfectScalarDualTensor l E P).homology 1,
      x ∈ Submodule.torsion (Padic.coefficientExtensionIntegers l E) _ →
        Padic.coefficientExtensionUniformizer l E ^ e • x = 0 := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  rcases h with ⟨hO, hm, hu, hlocal, hmax, huniq, hfrac, hdvr, hpid, hm0,
    hprime, hfinite, hr, hgen, hrest⟩
  let A := Padic.coefficientExtensionIntegers l E
  let : IsLocalRing A := hlocal
  let : IsDiscreteValuationRing A := hdvr
  let : IsPrincipalIdealRing A := hpid
  let H := (internalPerfectScalarDualTensor l E P).homology 1
  let : Module.Finite A H := finite_dual_tensor_homology P a b ha hb hp
  let π := Padic.coefficientExtensionUniformizer l E
  have hπ : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr
    ((IsLocalRing.eq_maximalIdeal hmax).symm.trans hgen.choose_spec.symm)
  obtain ⟨e, he⟩ := Submodule.exists_pow_smul_eq_zero_of_isNoetherian (A := H) π
  refine ⟨e, fun x hx ↦ he x ?_⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_torsion_iff x).mp hx
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.coe_ne_zero c) hπ
  refine ⟨n, ?_⟩
  change (c : A) • x = 0 at hc
  rw [hv, mul_smul] at hc
  exact v.isUnit.smul_eq_zero.mp hc

end AlgebraicGeometry.ProEtale
