import Langlands.GroupScheme.Rational.MaximalTorusConjugatorCaseCConjugator
import Langlands.GroupScheme.Lie.GenericNoncentral
import Langlands.GroupScheme.Lie.TorusCentralizerSliceBaseChange
import Langlands.GroupScheme.Lie.TorusLieCentralizerStatements
import Langlands.GroupScheme.Lie.PrimePowerFieldExtension
import Langlands.GroupScheme.Lie.PrimePowerCentralizer
import Langlands.GroupScheme.Lie.ScalarExtensionCoordinates
import Langlands.GroupScheme.Lie.SemisimpleCentralizerSmooth
import Langlands.GroupScheme.AffineCartierSmoothProof
import Langlands.GroupScheme.Rational.MaximalTorusGenericConjugatorInduction
import Langlands.GroupScheme.Rational.RationalFunctionFieldAlgebra
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Dynamic.RepresentedStructure
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.Torus.BaseChange

/-! # Generic conjugation data for Case C -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme


local instance caseCDataIsAffineHom {k E : Type u} [CommRing k] [CommRing E] [Algebra k E]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k E))
  infer_instance

local instance caseCDataLocallyOfFiniteType {k E : Type u} [CommRing k] [CommRing E]
    [Algebra k E] {G : GroupScheme (Spec (CommRingCat.of k))} [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change LocallyOfFiniteType (pullback.snd G.X.hom (algebraBaseMap k E))
  infer_instance

local instance caseCDataSmooth {k E : Type u} [CommRing k] [CommRing E] [Algebra k E]
    {G : GroupScheme (Spec (CommRingCat.of k))} [Smooth G.X.hom] :
    Smooth ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change Smooth (pullback.snd G.X.hom (algebraBaseMap k E))
  infer_instance

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {T₀ : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A **generic centralizer conjugator** for `j₀ : T₀ ⟶ G`: a field `K` over `k` whose rational
function fields are rational function fields over `k`, and a `K`-rational Lie element `Y` of
the base change `G_K` whose centralizer group is smooth and whose Lie centralizer is not all of
the Lie algebra, together with a centralizer conjugator for `Y`. -/
def HasGenericCentralizerConjugator [LocallyOfFiniteType G.X.hom] (j₀ : T₀.toGrp ⟶ G) : Prop :=
  ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
    ReducesRationalFunctionFields (algebraBaseMap k K) ∧
    ∃ Y : lieKernel ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) K,
      Smooth (Lie.elementCentralizerGroup
        ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) Y).X.hom ∧
      Lie.elementCentralizerLie ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) Y ≠ ⊤ ∧
      HasCentralizerConjugator G j₀ Y

variable {d : ℕ}

/-- The extension of `k` to the function field of `𝔸^d` reduces rational function fields. -/
theorem reducesRationalFunctionFields_genericField :
    ReducesRationalFunctionFields
      (algebraBaseMap k (𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k))).functionField) := by
  rw [algebraBaseMap_rationalFunctionField]
  exact reducesRationalFunctionFields_rationalFunctionFieldOver k _

/-- **A conjugate of the generic Lie element in the torus-centralizer slice.** Let `j₀` be a
maximal torus of a smooth connected affine group `G` with finite Lie coordinates `c`. There are
an algebraically closed field `Ω` over `k`, an embedding `ψ` of the function field of `𝔸^d`
into `Ω`, a point `g` of `G` over `Ω` with dense image, and a Lie element `Z` of `G` over `Ω`
such that `g` conjugates `Z` to the image of the generic Lie element under `ψ`, and the Lie
algebra of the base change of `T₀` to `Ω` lies in the Lie centralizer of `Z` in `G_Ω`. -/
theorem exists_conjugate_genericLieElement [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (c : Lie.FiniteCoordinates G d) {j₀ : T₀.toGrp ⟶ G} (hj₀ : IsMaximalTorus j₀) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : Algebra k Ω) (_ : IsAlgClosed Ω)
      (ψ : (𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k))).functionField →ₐ[k] Ω)
      (g : Lie.AffinePoints G Ω) (Z : lieKernel G Ω),
      DenseRange g.left ∧
      adjoint G Ω g (Additive.ofMul Z) = lieKernelMapLinear G ψ (Lie.genericLieElement c) ∧
      ∀ t : lieKernel ((GroupScheme.baseChange (algebraBaseMap k Ω)).obj T₀.toGrp)
          (CommRingCat.of Ω),
        Additive.ofMul
            (Lie.targetMap ((GroupScheme.baseChange (algebraBaseMap k Ω)).map j₀) _ t) ∈
          Lie.elementCentralizerLie ((GroupScheme.baseChange (algebraBaseMap k Ω)).obj G)
            ((Lie.kernelBaseChangeEquiv k Ω G Ω).symm Z) := by
  have : IrreducibleSpace G.X.left := DynamicConnected.irreducibleSpace_of_smooth G
  have : IsAffineHom T₀.toGrp.X.hom := hj₀.2.1.isAffineHom
  have : LocallyOfFiniteType T₀.toGrp.X.hom := hj₀.2.1.locallyOfFiniteType
  obtain ⟨r, B, hB, hdense⟩ := Lie.exists_torusCentralizerSlice c j₀ hj₀.1
  obtain ⟨L, _, _, φ, g, Z, hgen, ⟨s, hs⟩, hgZ⟩ :=
    Lie.exists_adjoint_eq_genericLieElement_of_denseRange c B hdense
  let e : L →ₐ[k] AlgebraicClosure L := IsScalarTower.toAlgHom k L (AlgebraicClosure L)
  have hZ : c.equiv (.of (CommRingCat.of k) (AlgebraicClosure L)) (lieKernelMapLinear G e Z) ∈
      Set.range (B.map (algebraMap k (AlgebraicClosure L))).mulVec := by
    refine ⟨e ∘ s, ?_⟩
    have hn := c.naturality (CommAlgCat.ofHom e :
      CommAlgCat.of (CommRingCat.of k) L ⟶ CommAlgCat.of (CommRingCat.of k) (AlgebraicClosure L)) Z
    change _ = c.equiv (.of (CommRingCat.of k) (AlgebraicClosure L))
      (lieKernelMapLinear G (CommAlgCat.ofHom e :
        CommAlgCat.of (CommRingCat.of k) L ⟶
          CommAlgCat.of (CommRingCat.of k) (AlgebraicClosure L)).hom Z)
    rw [hn, ← hs]
    funext i
    change _ = (e.toRingHom : L →+* AlgebraicClosure L) _
    have hBm : ⇑e.toRingHom ∘ ⇑(algebraMap k L) = ⇑(algebraMap k (AlgebraicClosure L)) :=
      funext e.commutes
    rw [RingHom.map_mulVec, Matrix.map_map, hBm]
    rfl
  refine ⟨AlgebraicClosure L, inferInstance, inferInstance, inferInstance, e.comp φ,
    Lie.affineMap G e g, (lieKernelMapLinear G e Z).toMul, ?_, ?_, fun t =>
      Lie.targetMap_mem_elementCentralizerLie_baseChange_of_mulVec c j₀ B hB _ hZ t⟩
  · have hmem : genericPoint G.X.left ∈ Set.range (Lie.affineMap G e g).left := by
      obtain ⟨x, hx⟩ := hgen
      refine ⟨IsLocalRing.closedPoint (AlgebraicClosure L), ?_⟩
      rw [← hx, Lie.affineMap_apply, Over.comp_left]
      change g.left (((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom e).op).left _) = _
      congr 1
      exact Subsingleton.elim (α := PrimeSpectrum L) _ _
    refine dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset ?_)
    rw [← (genericPoint_spec G.X.left).def]
    exact closure_mono (Set.singleton_subset_iff.2 hmem)
  · rw [lieKernelMapLinear_comp, ← hgZ, adjoint_naturality]
    rfl

variable [LocallyOfFiniteType G.X.hom]

/-- A Lie element whose adjoint differential is not nilpotent is not central. -/
theorem elementCentralizerLie_ne_top_of_not_isNilpotent {K : Type u} [Field K]
    {H : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom H.X.hom]
    [LocallyOfFiniteType H.X.hom] {e : ℕ} (cH : Lie.FiniteCoordinates H e) (X : lieKernel H K)
    (hX : ¬ IsNilpotent (Lie.adjointDifferentialFamily cH (Additive.ofMul X))) :
    Lie.elementCentralizerLie H X ≠ ⊤ := fun htop =>
  hX ((Lie.elementCentralizerLie_eq_top_iff_adjointDifferential_eq_zero cH X).1 htop ▸
    IsNilpotent.zero)

/-- Assembling a generic centralizer conjugator from its components. -/
theorem hasGenericCentralizerConjugator_of {j₀ : T₀.toGrp ⟶ G} {K : Type u} [Field K]
    [Algebra k K] (hK : ReducesRationalFunctionFields (algebraBaseMap k K))
    (Y : lieKernel ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) K)
    (hsm : Smooth (Lie.elementCentralizerGroup
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) Y).X.hom)
    (hne : Lie.elementCentralizerLie ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) Y ≠ ⊤)
    (hc : HasCentralizerConjugator G j₀ Y) : HasGenericCentralizerConjugator j₀ :=
  ⟨K, _, _, hK, Y, hsm, hne, hc⟩

/-- **The generic conjugation situation.** For a maximal torus `j₀` of a smooth connected affine
group `G` with a noncentral geometric semisimple Lie element, there are a field `K` over `k`
reducing rational function fields, a Lie element `X` of `G` over `K` whose adjoint differential
in `G_K` is not nilpotent, an algebraically closed field `Ω` with an embedding `ψ : K → Ω`, a
point `g` of `G` over `Ω` with dense image, and a Lie element `Z` of `G` over `Ω` such that `g`
conjugates `Z` to the image of `X`, and the Lie algebra of `T₀` over `Ω` centralizes `Z`. -/
theorem exists_generic_conjugate [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (c : Lie.FiniteCoordinates G d) {j₀ : T₀.toGrp ⟶ G} (hj₀ : IsMaximalTorus j₀)
    (hS : HasNoncentralGeometricSemisimpleElement G) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      ReducesRationalFunctionFields (algebraBaseMap k K) ∧
      ∃ X : lieKernel G K,
        ¬ IsNilpotent (Lie.adjointDifferentialFamily (c.baseChange k K)
          (Additive.ofMul ((Lie.kernelBaseChangeEquiv k K G K).symm X))) ∧
      ∃ (Ω : Type u) (_ : Field Ω) (_ : Algebra k Ω) (_ : IsAlgClosed Ω) (ψ : K →ₐ[k] Ω)
        (g : Lie.AffinePoints G Ω) (Z : lieKernel G Ω),
        DenseRange g.left ∧
        adjoint G Ω g (Additive.ofMul Z) = lieKernelMapLinear G ψ (Additive.ofMul X) ∧
        ∀ t : lieKernel ((GroupScheme.baseChange (algebraBaseMap k Ω)).obj T₀.toGrp)
            (CommRingCat.of Ω),
          Additive.ofMul
              (Lie.targetMap ((GroupScheme.baseChange (algebraBaseMap k Ω)).map j₀) _ t) ∈
            Lie.elementCentralizerLie ((GroupScheme.baseChange (algebraBaseMap k Ω)).obj G)
              ((Lie.kernelBaseChangeEquiv k Ω G Ω).symm Z) := by
  obtain ⟨Ω, _, _, _, ψ, g, Z, hg, hgZ, hZ⟩ := exists_conjugate_genericLieElement c hj₀
  refine ⟨(𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k))).functionField, inferInstance, inferInstance, reducesRationalFunctionFields_genericField,
    (Lie.genericLieElement c).toMul, ?_, Ω, inferInstance, inferInstance, inferInstance, ψ, g, Z,
    hg, hgZ, hZ⟩
  rw [Lie.adjointDifferentialFamily_apply, Lie.adjointRepresentation_baseChange_tangentMatrix,
    MulEquiv.apply_symm_apply]
  exact Lie.not_isNilpotent_tangentMatrix_genericLieElement c hS

/-- **Generic centralizer conjugators in characteristic `p`.** Assume the statement on
semisimple Lie elements commuting with the Lie algebra of a maximal torus and stability of
maximal tori under field extension. For a maximal torus `j₀` of a smooth connected affine group
`G` over a field of characteristic `p` with a noncentral geometric semisimple Lie element, a
field prime power of the generic Lie element has a generic centralizer conjugator. -/
theorem hasGenericCentralizerConjugator_of_charP
    (hW : SemisimpleMaximalTorusLieCentralizerStatement.{u})
    (hbc : MaximalTorusBaseChangeStatement.{u}) [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (p : ℕ) [Fact p.Prime] [CharP k p] (c : Lie.FiniteCoordinates G d) {j₀ : T₀.toGrp ⟶ G}
    (hj₀ : IsMaximalTorus j₀) (hS : HasNoncentralGeometricSemisimpleElement G) :
    HasGenericCentralizerConjugator j₀ := by
  obtain ⟨K, _, _, hK, X, hXn, Ω, _, _, _, ψ, g, Z, hg, hgZ, hZ⟩ :=
    exists_generic_conjugate c hj₀ hS
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  have : CharP Ω p := charP_of_injective_algebraMap (algebraMap k Ω).injective p
  obtain ⟨m, hX⟩ := exists_hasPrimePowerRelation X p
  have hgZ' : lieKernelConjugation G g Z = lieKernelMap G ψ X := congrArg Additive.toMul hgZ
  have hinv : lieKernelConjugation G g⁻¹ (lieKernelConjugation G g Z) = Z := by
    have h : adjoint G Ω g⁻¹ (adjoint G Ω g (Additive.ofMul Z)) = Additive.ofMul Z := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    exact congrArg Additive.toMul h
  have hZrel : HasPrimePowerRelation Z p m := by
    have h := (hX.map ψ).conjugation g⁻¹
    rwa [← hgZ', hinv] at h
  have hgZ'' : adjoint G Ω g (Additive.ofMul (fieldPrimePower k Ω G Z p m)) =
      lieKernelMapLinear G ψ (Additive.ofMul (fieldPrimePower k K G X p m)) := by
    change Additive.ofMul (lieKernelConjugation G g (fieldPrimePower k Ω G Z p m)) =
      Additive.ofMul (lieKernelMap G ψ (fieldPrimePower k K G X p m))
    rw [lieKernelConjugation_fieldPrimePower, hgZ', lieKernelMap_fieldPrimePower]
  have hLie : ∀ t : lieKernel ((GroupScheme.baseChange (algebraBaseMap k Ω)).obj T₀.toGrp)
      (CommRingCat.of Ω),
      Additive.ofMul
          (Lie.targetMap ((GroupScheme.baseChange (algebraBaseMap k Ω)).map j₀) _ t) ∈
        Lie.elementCentralizerLie ((GroupScheme.baseChange (algebraBaseMap k Ω)).obj G)
          ((Lie.kernelBaseChangeEquiv k Ω G Ω).symm (fieldPrimePower k Ω G Z p m)) := by
    intro t
    have hpp : (Lie.kernelBaseChangeEquiv k Ω G Ω).symm (fieldPrimePower k Ω G Z p m) =
        Lie.primePowerKernel ((GroupScheme.baseChange (algebraBaseMap k Ω)).obj G)
          ((Lie.kernelBaseChangeEquiv k Ω G Ω).symm Z) p m :=
      MulEquiv.symm_apply_apply _ _
    rw [hpp]
    exact Lie.elementCentralizerLie_le_primePowerKernel (c.baseChange k Ω) _ p m (hZ t)
  have : ConnectedSpace ((GroupScheme.baseChange (algebraBaseMap k Ω)).obj G).X.left :=
    GroupScheme.connectedSpace_baseChange_of_smooth_affine G (algebraBaseMap k Ω)
  have hmax : IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj T₀)
      ((GroupScheme.baseChange (algebraBaseMap k Ω)).map j₀) :=
    (hbc k Ω G T₀ j₀ hj₀.1 hj₀.2.1).1 hj₀
  have hfix := hW Ω ((GroupScheme.baseChange (algebraBaseMap k Ω)).obj G)
    ((CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj T₀)
    ((GroupScheme.baseChange (algebraBaseMap k Ω)).map j₀) hmax
    ((Lie.kernelBaseChangeEquiv k Ω G Ω).symm (fieldPrimePower k Ω G Z p m))
    hZrel.isSemisimpleElement hLie
  have hcon := hasCentralizerConjugator_of_adjoint_eq ψ (fieldPrimePower k K G X p m) g
    (fieldPrimePower k Ω G Z p m) hgZ'' (rangeFixesLieElement_of_range_le _ hfix) hg
  have hpp : (Lie.kernelBaseChangeEquiv k K G K).symm (fieldPrimePower k K G X p m) =
      Lie.primePowerKernel ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)
        ((Lie.kernelBaseChangeEquiv k K G K).symm X) p m :=
    MulEquiv.symm_apply_apply _ _
  have hne : Lie.elementCentralizerLie ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)
      ((Lie.kernelBaseChangeEquiv k K G K).symm (fieldPrimePower k K G X p m)) ≠ ⊤ := by
    rw [hpp]
    exact Lie.elementCentralizerLie_primePowerKernel_ne_top (c.baseChange k K) _ p m hXn
  exact hasGenericCentralizerConjugator_of hK _
    (Lie.smooth_elementCentralizerGroup _ hX.isSemisimpleElement) hne hcon

/-- **Generic centralizer conjugators in characteristic zero.** Assume the statement on tori
centralizing Lie elements in characteristic zero. For a maximal torus `j₀` of a smooth connected
affine group `G` over a field of characteristic zero with a noncentral geometric semisimple Lie
element, the generic Lie element has a generic centralizer conjugator. -/
theorem hasGenericCentralizerConjugator_of_charZero
    (hW0 : CharZeroTorusLieCentralizerStatement.{u}) [CharZero k] [Smooth G.X.hom]
    [ConnectedSpace G.X.left] (c : Lie.FiniteCoordinates G d) {j₀ : T₀.toGrp ⟶ G}
    (hj₀ : IsMaximalTorus j₀) (hS : HasNoncentralGeometricSemisimpleElement G) :
    HasGenericCentralizerConjugator j₀ := by
  obtain ⟨K, _, _, hK, X, hXn, Ω, _, _, _, ψ, g, Z, hg, hgZ, hZ⟩ :=
    exists_generic_conjugate c hj₀ hS
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  have hfix := hW0 Ω ((GroupScheme.baseChange (algebraBaseMap k Ω)).obj G)
    ((CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj T₀)
    ((GroupScheme.baseChange (algebraBaseMap k Ω)).map j₀) (IsTorus.baseChange hj₀.1)
    ((Lie.kernelBaseChangeEquiv k Ω G Ω).symm Z) hZ
  have hcon := hasCentralizerConjugator_of_adjoint_eq ψ X g Z hgZ
    (rangeFixesLieElement_of_range_le Z hfix) hg
  have hcl := Lie.isClosedSubgroup_elementCentralizerGroupι
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    ((Lie.kernelBaseChangeEquiv k K G K).symm X)
  exact hasGenericCentralizerConjugator_of hK _
    (affineCartierSmooth K _ hcl.isAffineHom hcl.locallyOfFiniteType)
    (elementCentralizerLie_ne_top_of_not_isNilpotent (c.baseChange k K) _ hXn) hcon

/-- **Generic conjugation data for Case C**, assuming the statements on tori centralizing Lie
elements (semisimple elements over algebraically closed fields, and characteristic zero) and
stability of maximal tori under field extension. -/
theorem semisimpleCentralizerConjugationData
    (hW : SemisimpleMaximalTorusLieCentralizerStatement.{u})
    (hW0 : CharZeroTorusLieCentralizerStatement.{u})
    (hbc : MaximalTorusBaseChangeStatement.{u}) :
    SemisimpleCentralizerConjugationDataStatement.{u} := by
  intro k _ G _ _ _ T₀ j₀ hj₀ hS
  have h : HasGenericCentralizerConjugator j₀ := by
    obtain ⟨p, hp⟩ := CharP.exists k
    rcases CharP.char_is_prime_or_zero k p with hpp | rfl
    · have : Fact p.Prime := ⟨hpp⟩
      exact hasGenericCentralizerConjugator_of_charP hW hbc p (Lie.finiteCoordinates G) hj₀ hS
    · have : CharZero k := @CharP.charP_to_charZero k _ hp
      exact hasGenericCentralizerConjugator_of_charZero hW0 (Lie.finiteCoordinates G) hj₀ hS
  obtain ⟨K, _, _, hK, Y, hsm, hY, hc⟩ := h
  exact ⟨K, _, _, hK, conjugationData_of_hasCentralizerConjugator hj₀ hY hc⟩

end Langlands.GroupScheme
