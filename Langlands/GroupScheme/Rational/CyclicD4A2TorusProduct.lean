import Langlands.GroupScheme.Rational.CyclicD4A2DerivedFace
import Langlands.GroupScheme.Rational.GaloisBorelFaceTorusProduct

/-! # The torus product of the two cyclic A2 faces in type D4 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open Langlands.LinearAlgebra Langlands.RootDatumSimpleCorootEquiv

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 950000
set_option maxRecDepth 3000

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {p : GaloisPinningData F K G}

attribute [local instance] GaloisBorelFaceDerived.derivedAffine GaloisBorelFaceDerived.derivedFiniteType

local notation "BC" => CommGroupScheme.baseChange (algebraBaseMap F K)

namespace CyclicD4A2DerivedFace

variable {i j : p.rootIndex} (A : CyclicD4A2DerivedFace p i j)

omit [LocallyOfFiniteType G.X.hom] in
/-- The numbered simple coroots of the factor are the prescribed ambient pair. -/
theorem coroot_comp_torusMap (k : Fin 2) :
    A.roots.rootDatum.coroot (A.simple k).val ≫ (BC).map A.groups.torusMap =
      p.rootDatum.coroot (![i, j] k) := by
  rw [A.roots.coroot_comp_torusMap]
  change p.rootDatum.coroot (A.roots.simpleEquiv (A.simple k)).val.val = _
  fin_cases k
  · exact congrArg p.rootDatum.coroot A.simple_first
  · exact congrArg p.rootDatum.coroot A.simple_second

end CyclicD4A2DerivedFace

/-- The two actual A2 faces of the cubic-split maximal torus and the
isomorphism obtained by multiplying their induced tori. -/
structure CyclicD4A2TorusFactors (p : GaloisPinningData F K G) where
  firstRoot : p.rootIndex
  secondRoot : p.rootIndex
  generator : K ≃ₐ[F] K
  first : CyclicD4A2DerivedFace p firstRoot ((p.galoisAction generator).indexEquiv firstRoot)
  second : CyclicD4A2DerivedFace p secondRoot ((p.galoisAction generator).indexEquiv secondRoot)
  product_isIso : IsIso (CommGroupScheme.prodFst first.groups.torus second.groups.torus ≫
    first.groups.torusMap + CommGroupScheme.prodSnd first.groups.torus second.groups.torus ≫
    second.groups.torusMap)

variable (p)

/-- An anisotropic simply connected group of type D4 with a supplied
cubic-split maximal torus has the two descended derived-torus factors. -/
theorem GaloisPinningData.nonempty_cyclicD4A2TorusFactors [FiniteDimensional F K] [IsGalois F K]
    (hsc : IsSimplyConnected G) (ht : IsMaximalTorus p.inclusion) (han : IsAnisotropic G)
    (hdeg : Module.finrank F K = 3) (e : p.base.support ≃ Fin 4)
    (hD : ∀ v w : p.base.support, p.rootDatum.pairing v.val w.val = CartanMatrix.D 4 (e v) (e w)) :
    Nonempty (CyclicD4A2TorusFactors p) := by
  obtain ⟨σ, hσ⟩ := exists_cubic_galois_generator hdeg
  let i := (e.symm 0).val
  let s := (p.galoisAction σ).indexEquiv
  let : p.rootDatum.IsReduced := p.isReduced
  have hspan := p.corootSpan_eq_top_of_simplyConnected hsc
  obtain ⟨j, hli, hsp⟩ := exists_d4CyclicPair_integralBasis p.rootDatum p.base hspan e hD s
    (fun _ _ => (p.galoisAction σ).toHom.pairing) (p.cyclic_rootIndex_cube σ hσ)
    (p.coroot_cyclic_norm_eq_zero ht han hdeg σ hσ) (p.galoisAction σ).symm.coweightEquiv
    (p.galoisAction_coweightEquiv_symm_coroot σ) i
  obtain ⟨A⟩ := p.nonempty_cyclicD4A2DerivedFace hsc ht han hdeg e hD σ hσ i
  obtain ⟨B⟩ := p.nonempty_cyclicD4A2DerivedFace hsc ht han hdeg e hD σ hσ j.val
  let U := Module.Basis.mk hli (le_of_eq hsp.symm)
  let V₀ := simpleCorootBasis A.roots.face.base
    (A.roots.pinning.corootSpan_eq_top_of_simplyConnected A.groups.isSimplyConnected)
  let W₀ := simpleCorootBasis B.roots.face.base
    (B.roots.pinning.corootSpan_eq_top_of_simplyConnected B.groups.isSimplyConnected)
  let V := V₀.reindex A.simple.symm
  let W := W₀.reindex B.simple.symm
  let eSum : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv
  have hA (k : Fin 2) :
      V k ≫ (BC).map A.groups.torusMap = U (eSum (Sum.inl k)) := by
    simp only [V, V₀, Module.Basis.reindex_apply, Equiv.symm_symm, simpleCorootBasis_apply,
      A.coroot_comp_torusMap, U, Module.Basis.mk_apply]
    fin_cases k <;> rfl
  have hB (k : Fin 2) :
      W k ≫ (BC).map B.groups.torusMap = U (eSum (Sum.inr k)) := by
    simp only [W, W₀, Module.Basis.reindex_apply, Equiv.symm_symm, simpleCorootBasis_apply,
      B.coroot_comp_torusMap, U, Module.Basis.mk_apply]
    fin_cases k <;> rfl
  exact ⟨⟨i, j.val, σ, A, B, isIso_torusProduct_of_character_restrictions
    A.groups.torusMap B.groups.torusMap p.isSplitTorus A.roots.isSplit B.roots.isSplit
    (character_restriction_bijective_of_bases p.isSplitTorus A.roots.isSplit B.roots.isSplit
      ((BC).map A.groups.torusMap) ((BC).map B.groups.torusMap) U V W eSum hA hB)⟩⟩

end Langlands.GroupScheme
