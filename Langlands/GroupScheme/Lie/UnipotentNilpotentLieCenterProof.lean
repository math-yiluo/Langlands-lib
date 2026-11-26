import Langlands.GroupScheme.Lie.UnipotentNilpotentLieCenterStatement
import Langlands.GroupScheme.Lie.AffineBracketAdjoint
import Langlands.GroupScheme.Lie.PrimePowerFieldExtension
import Langlands.GroupScheme.Lie.SemisimpleNilpotentMatrix
import Langlands.GroupScheme.Lie.SplitTorusSemisimple
import Langlands.GroupScheme.Lie.ZeroTangentTriviality
import Langlands.GroupScheme.Absolute.KernelMaximalTorusUnipotent
import Langlands.GroupScheme.Rational.ActionLieRigidity
import Langlands.GroupScheme.Rational.RootSubgroupVectorTransport
import Langlands.GroupScheme.Torus.MultiplicativeTypeUnipotentHom
import Langlands.GroupScheme.Torus.NoTorusUnipotent
import Langlands.GroupScheme.Torus.RelativeFieldComparison
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeCentralizerModel
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeFieldComparison
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeSubgroupProof
import Langlands.GroupScheme.Torus.RelativeTorusMultiplicativeType
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Mathlib.Algebra.Lie.Engel
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Unipotence via the full centre and the tangent Lie algebra -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

/-- Two elements with the same image under ring equivalences are nilpotent
together. -/
private theorem isNilpotent_iff_of_ringEquiv_eq {A B C : Type*}
    [Semiring A] [Semiring B] [Semiring C]
    (f : A ≃+* C) (g : B ≃+* C) {x : A} {y : B} (h : f x = g y) :
    IsNilpotent x ↔ IsNilpotent y := by
  rw [← IsNilpotent.map_iff (f := f) f.injective, h, IsNilpotent.map_iff g.injective]

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]

set_option maxHeartbeats 600000 in
/-- In finite tangent coordinates, Engel's criterion is nilpotence of all actual
adjoint tangent matrices. -/
private theorem lieRing_isNilpotent_iff_adjoint_tangent {d : ℕ} (c : FiniteCoordinates G d) :
    letI := instAffineKernelLieRing (R := CommRingCat.of k) (A := CommRingCat.of k) G
    LieRing.IsNilpotent (Additive (lieKernel G (CommRingCat.of k))) ↔
      ∀ X : lieKernel G (CommRingCat.of k),
        IsNilpotent ((adjointRepresentation c).tangentMatrix (CommRingCat.of k) X) := by
  let := instAffineKernelLieRing (R := CommRingCat.of k) (A := CommRingCat.of k) G
  let := instAffineKernelLieAlgebra (R := CommRingCat.of k) (A := CommRingCat.of k) G
  let e := c.equiv (CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k))
  let : IsNoetherian (CommRingCat.of k) (Additive (lieKernel G (CommRingCat.of k))) :=
    isNoetherian_of_linearEquiv e.symm
  rw [LieAlgebra.isNilpotent_iff_forall (R := CommRingCat.of k)]
  let E := e.conjAlgEquiv (CommRingCat.of k)
  let M : Matrix (Fin d) (Fin d) (CommRingCat.of k) ≃ₐ[CommRingCat.of k]
      Module.End (CommRingCat.of k) (Fin d → CommRingCat.of k) := Matrix.toLinAlgEquiv'
  have hconj (X : Additive (lieKernel G (CommRingCat.of k))) :
      E (LieAlgebra.ad (CommRingCat.of k) _ X) = M
        ((adjointRepresentation c).tangentMatrix (CommRingCat.of k) X.toMul) := by
    apply LinearMap.ext
    intro v
    obtain ⟨Y, rfl⟩ := e.surjective v
    rw [LinearEquiv.conjAlgEquiv_apply_apply, LinearEquiv.symm_apply_apply, LieAlgebra.ad_apply]
    exact (adjointDifferentialLieHom_apply_bracket c X Y).symm
  have hnil (X : Additive (lieKernel G (CommRingCat.of k))) :
      IsNilpotent (LieAlgebra.ad (CommRingCat.of k) _ X) ↔
        IsNilpotent ((adjointRepresentation c).tangentMatrix (CommRingCat.of k) X.toMul) :=
    isNilpotent_iff_of_ringEquiv_eq E.toRingEquiv M.toRingEquiv (hconj X)
  exact ⟨fun h X => (hnil (Additive.ofMul X)).mp (h (Additive.ofMul X)),
    fun h X => (hnil X).mpr (h X.toMul)⟩

/-- A nilpotent tangent matrix of a torus representation is zero. -/
private theorem tangentMatrix_eq_zero_of_isTorus
    {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsTorus T)
    {d : ℕ} (ρ : MatrixRepresentation T (Fin d)) (X : lieKernel T k)
    (hN : IsNilpotent (ρ.tangentMatrix k X)) : ρ.tangentMatrix k X = 0 := by
  obtain ⟨K, _, _, hsplit⟩ := hT
  let XK := (kernelBaseChangeEquiv k K T K).symm
    (lieKernelMap T (Algebra.ofId k K) X)
  have hbase : (ρ.baseChange (algebraBaseMap k K)).tangentMatrix K XK =
      (algebraMap k K).mapMatrix (ρ.tangentMatrix k X) := by
    rw [ρ.tangentMatrix_baseChange]
    dsimp only [XK]
    rw [MulEquiv.apply_symm_apply, ρ.tangentMatrix_naturality]
    rfl
  have hsem := isSemisimpleElement_of_isSplitTorus hsplit XK d
    (ρ.baseChange (algebraBaseMap k K))
  rw [hbase] at hsem
  have hz := hsem.eq_zero_of_isNilpotent (hN.map (algebraMap k K).mapMatrix)
  apply Matrix.map_injective (algebraMap k K).injective
  exact hz.trans (map_zero (algebraMap k K).mapMatrix).symm

variable [ConnectedSpace G.X.left]

/-- A multiplicative-type group acting trivially through the actual adjoint
representation maps into the full centre. -/
private theorem isCentral_of_adjoint_eq_zero
    {H : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : H.toGrp ⟶ G) (hH : RelativeMultiplicativeType.IsMultiplicativeType H.toGrp)
    {d : ℕ} (c : FiniteCoordinates G d) (hi : i ≫ adjointRepresentation c = 0) :
    IsCentral i := by
  obtain ⟨C, j, hj, hs, hrep⟩ := relativeMultiplicativeTypeCentralizerModel i hH
  apply (isCentral_iff_torusCentralizer_eq_top i).mpr
  apply RelativeRoot.eq_top_of_smooth_closed_of_tangentSubmodule_eq_top j hrep hj hs
  rw [← AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer,
    AutomorphicAction.tangentSubmodule_fixedSubgroup]
  apply top_unique
  intro X _ A _ _ t
  rw [AutomorphicAction.differential_conjugation]
  let S := CommAlgCat.of (CommRingCat.of k) A
  apply (c.equiv S).injective
  rw [← adjointRepresentation_affineAction]
  have he : (adjointRepresentation c).restrict i = MatrixRepresentation.trivial H.toGrp (Fin d) :=
    hi
  have hv := congrArg (fun ρ => ρ.affineAction S t) he
  rw [MatrixRepresentation.affineAction_restrict, MatrixRepresentation.trivial_affineAction] at hv
  rw [hv]
  rfl

/-- The adjoint representation restricts to a monomorphism on a closed torus
when the ambient group's full centre is unipotent. -/
private theorem adjointRestriction_mono {d : ℕ} (c : FiniteCoordinates G d)
    {Z : GroupScheme (Spec (CommRingCat.of k))} (z : Z ⟶ G) (hz : IsClosedSubgroup z)
    (hrep : (center G).IsRepresentedBy z) (hZ : IsUnipotent Z)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)
    (hT : IsTorus T.toGrp) (hi : IsClosedSubgroup i) :
    Mono ((adjointRepresentation c).restrict i).hom.hom := by
  let σ := (adjointRepresentation c).restrict i
  let K : CommGroupScheme (Spec (CommRingCat.of k)) := { toGrp := kernel σ }
  have hκ : IsClosedSubgroup (kernelι σ) := kernelι_isClosedImmersion σ
  let : IsClosedImmersion (kernelι σ).hom.hom.left := hκ
  let : Smooth T.toGrp.X.hom := hT.smooth
  let : LocallyOfFiniteType (kernel σ).X.hom := by
    rw [← Over.w (kernelι σ).hom.hom]
    infer_instance
  have hK : RelativeMultiplicativeType.IsMultiplicativeType K.toGrp :=
    relativeMultiplicativeTypeClosedSubgroup _ K.toGrp T.toGrp (kernelι σ)
      hT.isRelativeTorus.isMultiplicativeType hκ
      inferInstance inferInstance
  let j : K.toGrp ⟶ G := kernelι σ ≫ i
  have h0 : j ≫ adjointRepresentation c = 0 := by
    change (kernelι σ ≫ i) ≫ adjointRepresentation c = 0
    rw [Category.assoc]
    exact kernelι_comp_eq_zero σ
  have hc : IsCentral j := isCentral_of_adjoint_eq_zero j hK c h0
  let : Mono i.hom.hom := hi.mono_overHom
  let : Mono j.hom.hom := by
    change Mono ((kernelι σ).hom.hom ≫ i.hom.hom)
    infer_instance
  let : Mono z.hom.hom := hrep.1
  have hle : SubgroupFunctor.range j ≤ SubgroupFunctor.range z := by
    rw [hrep.2]
    rintro U _ ⟨x, rfl⟩
    exact hc U x
  obtain ⟨f, hf⟩ := SubgroupFunctor.exists_factor_of_range_le hle
  let : IsAffineHom Z.X.hom := hz.isAffineHom
  have hf0 := hK.isFieldMultiplicativeType.hom_eq_zero_of_isUnipotent hZ f
  have hj0 : j = 0 := by rw [← hf, hf0, zero_comp]
  have : Mono i := (Grp.forget _).mono_of_mono_map (f := i)
    (show Mono i.hom.hom from inferInstance)
  have hk0 : kernelι σ = 0 := by
    apply (cancel_mono i).mp
    rw [zero_comp]
    exact hj0
  apply SubgroupFunctor.mono_of_range_kernel_eq_bot σ
  rw [hk0, SubgroupFunctor.range_zero]

/-- Milne 16.61(a,b). A smooth connected affine group is unipotent exactly
when its full centre is unipotent and its tangent Lie algebra is nilpotent. -/
theorem unipotentNilpotentLieCenter : UnipotentNilpotentLieCenterStatement.{u} := by
  intro k _ G _ _ _ Z z hz hrep
  let c := finiteCoordinates G
  rw [lieRing_isNilpotent_iff_adjoint_tangent c]
  constructor
  · intro hG
    exact ⟨unipotentClosedSubgroup k G Z z hz hG,
      (adjointRepresentation c).isNilpotent_tangentMatrix_of_isUnipotent hG _⟩
  · rintro ⟨hZ, hN⟩
    apply noTorusUnipotent k G
    intro T hT e
    obtain ⟨H, i, f, hH, hi, hfac⟩ := torusImageClosedTorusStatement k G T.toGrp hT e
    let σ := (adjointRepresentation c).restrict i
    have hσ : Mono σ.hom.hom := adjointRestriction_mono c z hz hrep hZ i hH hi
    have hone (X : lieKernel H.toGrp k) : X = 1 := by
      have hnil : IsNilpotent (σ.tangentMatrix k X) := by
        rw [MatrixRepresentation.tangentMatrix_restrict]
        exact hN (targetMap i k X)
      apply σ.tangentMatrix_injective hσ k
      rw [σ.tangentMatrix_one, tangentMatrix_eq_zero_of_isTorus hH σ X hnil]
    let : Subsingleton (lieKernel H.toGrp k) := ⟨fun X Y => (hone X).trans (hone Y).symm⟩
    let : Smooth H.toGrp.X.hom := hH.smooth
    let : IsAffineHom H.toGrp.X.hom := hi.isAffineHom
    let : ConnectedSpace H.toGrp.X.left := hH.connectedSpace
    rw [← hfac]
    apply SubgroupFunctor.ext
    intro U
    rw [SubgroupFunctor.bot_carrier, Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    rw [Grp.comp_hom_hom, ← Category.assoc,
      points_eq_one_of_subsingleton_lieKernel H.toGrp U (y ≫ f.hom.hom), MonObj.one_comp]

end Langlands.GroupScheme.Lie
