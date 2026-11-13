import Langlands.GroupScheme.Reductive.SplitExistence
import Langlands.GroupScheme.Reductive.SplitCentralIsogenyExistenceProof
import Langlands.GroupScheme.CentralIsogeny.RestrictionIsomorphism
import Langlands.GroupScheme.Reductive.SplitSemisimplicity
import Langlands.LinearAlgebra.AdjointRootDatum

/-! # The roots of a split adjoint group span its character lattice -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.LinearAlgebra

section GeneralBase

variable {S : Scheme.{u}} {G H : GroupScheme S} {φ : G ⟶ H}

/-- A central isogeny out of a group scheme with trivial scheme-theoretic centre is an
isomorphism: its kernel is central, hence trivial, so it is a finite flat surjective
monomorphism. -/
theorem IsCentralIsogeny.isIso_of_center_eq_bot (hφ : IsCentralIsogeny φ)
    (hc : center G = ⊥) : IsIso φ := by
  have : Mono φ.hom.hom := by
    constructor
    intro U a b hab
    apply div_eq_one.mp
    have hk : (a / b) ≫ φ.hom.hom = 1 := by
      rw [GrpObj.div_comp, hab, div_self']
    have hz := hφ.mem_center_of_comp_eq_one hk
    rw [hc, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hz
    exact hz
  have : Mono φ.hom.hom.left := Over.mono_left_of_mono _
  have : IsFinite φ.hom.hom.left := hφ.isIsogeny.1
  have : Flat φ.hom.hom.left := hφ.isIsogeny.2.1
  have : Surjective φ.hom.hom.left := hφ.isIsogeny.2.2
  have : IsIso φ.hom.hom.left := Flat.isIso_of_surjective_of_mono _
  have : IsIso ((Over.forget S).map φ.hom.hom) := by
    change IsIso φ.hom.hom.left
    infer_instance
  have : IsIso φ.hom.hom := isIso_of_reflects_iso φ.hom.hom (Over.forget S)
  let e : G ≅ H := Grp.mkIso' (asIso φ.hom.hom)
  change IsIso e.hom
  infer_instance

end GeneralBase

/-- **The roots of a split adjoint group span its character lattice.** Let `G` be an adjoint
group over a field with a split maximal torus `i : T ⟶ G` and a finite reduced root datum `P`
of `i`. Then the roots of `P` span `X^*(T)` over `ℤ`.

The split group `G'` with the adjoint root datum `(ℤR, R, Hom(ℤR, ℤ), R^∨)` of `P`
(`splitReductiveExistence`) receives a central isogeny `G → G'` realizing the canonical
morphism of root data `AdjointRootDatum.fromRootDatum P` (`splitCentralIsogenyExistence`). As the
centre of `G` is trivial, the isogeny and its torus map are isomorphisms, so the inclusion of
the root lattice into `X^*(T)` is surjective. -/
theorem IsAdjoint.rootSpan_eq_top {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsAdjoint G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp)
    {i : T.toGrp ⟶ G} (hi : IsMaximalTorus i) {J : Type u} [Finite J]
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (hP : haveI := hG.isSemisimple.isConnectedReductive.isAffineHom; IsRootDatumOf i P)
    (hPred : P.IsReduced) : P.rootSpan ℤ = ⊤ := by
  have hGr := hG.isSemisimple.isConnectedReductive
  have := hGr.isAffineHom
  -- The roots of `P` span a subgroup of finite index in the character lattice.
  have hfin : Finite (characterLattice T ⧸ P.rootSpan ℤ) :=
    (splitSemisimpleRootDatum k G hGr T hT i hi J P hP).1.mp hG.isSemisimple
  -- The split group `G'` with the adjoint root datum of `P`.
  obtain ⟨G', hG', T', i', hT', hi', Q, hQ, ⟨e⟩⟩ :=
    splitReductiveExistence k J (P.rootSpan ℤ) (Module.Dual ℤ (P.rootSpan ℤ))
      (AdjointRootDatum.rootDatum P) inferInstance
  -- The central isogeny of root data `Q → P`.
  let f : RootPairing.Hom Q P := (AdjointRootDatum.fromRootDatum P).comp e.symm.toHom
  have hfw : Function.Injective f.weightMap :=
    (AdjointRootDatum.injective_fromRootDatum_weightMap P).comp
      e.symm.bijective_weightMap.injective
  have hfc : Function.Injective f.coweightMap :=
    e.symm.bijective_coweightMap.injective.comp
      (AdjointRootDatum.injective_fromRootDatum_coweightMap P hfin)
  obtain ⟨φ, t, hsq, hwt, hφ⟩ :=
    splitCentralIsogenyExistence k G G' hGr hG' T T' hT hT' i i' hi hi' J J P Q hP hQ f hfw hfc
  -- The centre of `G` is trivial, so the isogeny and its torus map are isomorphisms.
  have : IsIso φ := hφ.isIso_of_center_eq_bot hG.center_eq_bot
  have : IsIso t := IsMaximalTorus.isIso_factor_of_isIso hi hi'.1 hi'.2.1 φ t hsq
  -- Hence the weight map `X(T') → X(T)`, which factors through the root span, is surjective.
  rw [eq_top_iff]
  intro χ _
  have hχ : f.weightMap (inv t ≫ χ) = χ := by
    rw [hwt, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  rw [← hχ]
  exact (e.symm.toHom.weightMap (inv t ≫ χ)).property

end Langlands.GroupScheme
