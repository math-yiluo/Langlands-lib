/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import WeilConjectures.Mathlib.CategoryTheory.Yoneda

/-!
# Compatibility of Jacobian identifications with base change
Source: blueprint `proposition-cohomology-smooth-affine-curve--4`, proof step 3.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

-- The original instance binder is used through typeclass inference.
set_option linter.unusedVariables false in
/-- The compatibility square for two Jacobian representing objects after base change.
Source: blueprint `proposition-cohomology-smooth-affine-curve--4`, proof step 3 (Picard base-change
and Yoneda). Proof: on each test scheme T over K, the iterated-pullback isomorphism identifies
C_K ×_K T with C ×_k T. Pullback of invertible modules along this isomorphism preserves
fibrewise degree, because the two fibres and their Euler characteristics agree. Thus it
induces an isomorphism of degree-zero Picard presheaves. Restriction along Over.map b
commutes with fppf sheafification, since covers of T in the two slice sites are the same;
compose this comparison with the sheafification of the presheaf isomorphism to get E.
The units of sheafification commute with E, so E sends the class of L to the class of its
specified pullback. The adjunction Over.map b ⊣ Over.pullback b transports e to a
representation r of the restricted sheaf by J_K. Transport r along E, and compare it with
eK using uniqueness of representing objects (Yoneda). This gives i : JK ≅ J_K with
r.homEquiv (a ≫ i.hom) = eK.homEquiv a. Apply this to the classifying map of the
pullback of L, use the unit compatibility, and invert e.homEquiv. The inverse adjunction
sends a map to J_K to its composite with pullback.fst J.hom b, giving exactly the square.
This construction applies to arbitrary representing identifications, hence also to those
respecting the group laws. Identity extensions and genus-zero curves are included.
(blueprint: theorem-picard-scheme-jacobian-over-separably--5) -/
theorem jacobian_compatibility
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K] [Algebra k K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    [IsProper f] [GeometricallyIntegral f] :
    let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let fK := pullback.snd f b
    ∀ [hcurve : IsConnectedCurve fK],
    ∀ (J : Over (Spec (.of k))) [GrpObj J] [IsJacobian f J]
      (e : (picardFunctorDegree f 0).obj.RepresentableBy J), IsPicardZeroMul f e →
      ∀ (JK : Over (Spec (.of K))) [GrpObj JK] [IsJacobian fK JK]
        (eK : (picardFunctorDegree fK 0).obj.RepresentableBy JK), IsPicardZeroMul fK eK →
      ∃ i : JK ≅ Over.mk (pullback.snd J.hom b),
      ∀ (T : Over (Spec (.of K))) (L : (pullback f (T.hom ≫ b)).Pic)
        (hL : L ∈ (picardSubfunctorDegree f 0).obj (.op ((Over.map b).obj T))),
      ∃ hLK : Pic.map (pullbackLeftPullbackSndIso f b T.hom).hom L ∈
          (picardSubfunctorDegree fK 0).obj (.op T),
        (eK.homEquiv.symm ((toSheafify (Scheme.fppfTopology.over (Spec (.of K)))
          (picardSubfunctorDegree fK 0).toFunctor).app (.op T)
            ⟨Pic.map (pullbackLeftPullbackSndIso f b T.hom).hom L, hLK⟩)).left ≫
            i.hom.left ≫ pullback.fst J.hom b =
        (e.homEquiv.symm ((toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
          (picardSubfunctorDegree f 0).toFunctor).app (.op ((Over.map b).obj T))
            ⟨L, hL⟩)).left := by
  classical
  dsimp only
  intro _hcurve J _ _ e he JK _ _ eK heK
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let fK := pullback.snd f b
  let sq := IsPullback.of_hasPullback f b
  let eP := picardPresheafIsoOfIsPullback sq
  have hiso (T : Over (Spec (.of K))) :
      (pullbackIsoOfIsPullback sq T).hom =
        (pullbackLeftPullbackSndIso f b T.hom).hom := by
    apply pullback.hom_ext <;> simp
  have hmem (T : Over (Spec (.of K)))
      (L : (picardPresheaf f).obj (.op ((Over.map b).obj T))) :
      L ∈ (picardSubfunctorDegree f 0).obj (.op ((Over.map b).obj T)) ↔
        eP.hom.app (.op T) L ∈ (picardSubfunctorDegree fK 0).obj (.op T) := by
    change L ∈ (picardSubfunctorDegree f 0).obj (.op ((Over.map b).obj T)) ↔
      Pic.map (pullbackIsoOfIsPullback sq T).hom L ∈
        (picardSubfunctorDegree fK 0).obj (.op T)
    rw [mem_picardSubfunctorDegree_iff, mem_picardSubfunctorDegree_iff]
    refine forall_congr' fun t ↦ ?_
    rw [picardPresheafDegree_pic_map_of_isPullback f fK (𝟙 T.left) _
        (IsPullback.of_horiz_isIso ⟨by simp [fK]⟩) L t]
    rfl
  let eS : (Over.map b).op ⋙ (picardSubfunctorDegree f 0).toFunctor ≅
      (picardSubfunctorDegree fK 0).toFunctor :=
    NatIso.ofComponents
      (fun T ↦ Equiv.toIso ((eP.app T).toEquiv.subtypeEquiv fun L ↦ hmem T.unop L))
      fun {T T'} φ ↦ by
        ext L
        apply Subtype.ext
        exact NatTrans.naturality_apply eP.hom φ L.1
  let E : (Over.map b).op ⋙ (picardFunctorDegree f 0).obj ≅
      (picardFunctorDegree fK 0).obj :=
    overMapOpCompSheafifyIso b _ ≪≫
      (sheafToPresheaf _ _).mapIso ((presheafToSheaf _ _).mapIso eS)
  let r := (e.ofAdjunction (Over.mapPullbackAdj b)).ofIso E
  let i := eK.uniqueUpToIso r
  refine ⟨i, ?_⟩
  intro T L hL
  have hLK : Pic.map (pullbackLeftPullbackSndIso f b T.hom).hom L ∈
      (picardSubfunctorDegree fK 0).obj (.op T) := by
    have h := (hmem T L).mp hL
    change Pic.map (pullbackIsoOfIsPullback sq T).hom L ∈ _ at h
    rwa [hiso] at h
  refine ⟨hLK, ?_⟩
  let x := (toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
    (picardSubfunctorDegree f 0).toFunctor).app (.op ((Over.map b).obj T)) ⟨L, hL⟩
  let y := (toSheafify (Scheme.fppfTopology.over (Spec (.of K)))
    (picardSubfunctorDegree fK 0).toFunctor).app (.op T)
      ⟨Pic.map (pullbackLeftPullbackSndIso f b T.hom).hom L, hLK⟩
  have hbc : toSheafify (Scheme.fppfTopology.over (Spec (.of K)))
      ((Over.map b).op ⋙ (picardSubfunctorDegree f 0).toFunctor) ≫
      (overMapOpCompSheafifyIso b (picardSubfunctorDegree f 0).toFunctor).inv =
      Functor.whiskerLeft (Over.map b).op
        (toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
          (picardSubfunctorDegree f 0).toFunctor) :=
    (Over.map b).toSheafify_pullbackSheafificationCompatibility _ _ _ _
  have hbc' :
      (overMapOpCompSheafifyIso b (picardSubfunctorDegree f 0).toFunctor).hom.app (.op T) x =
      (toSheafify (Scheme.fppfTopology.over (Spec (.of K)))
        ((Over.map b).op ⋙ (picardSubfunctorDegree f 0).toFunctor)).app (.op T) ⟨L, hL⟩ := by
    apply (overMapOpCompSheafifyIso b
      (picardSubfunctorDegree f 0).toFunctor).symm.app (.op T) |>.toEquiv.injective
    have h := congrArg (fun η ↦ η.app (.op T) ⟨L, hL⟩) hbc
    simpa [x] using h.symm
  have hunit : E.hom.app (.op T) x = y := by
    change (sheafifyMap (Scheme.fppfTopology.over (Spec (.of K))) eS.hom).app (.op T)
      ((overMapOpCompSheafifyIso b _).hom.app (.op T) x) = y
    rw [hbc']
    have h := congrArg (fun η ↦ η.app (.op T) ⟨L, hL⟩)
      (toSheafify_naturality (Scheme.fppfTopology.over (Spec (.of K))) eS.hom)
    have hv : eS.hom.app (.op T) ⟨L, hL⟩ =
        ⟨Pic.map (pullbackLeftPullbackSndIso f b T.hom).hom L, hLK⟩ := by
      apply Subtype.ext
      change Pic.map (pullbackIsoOfIsPullback sq T).hom L = _
      rw [hiso]
    simpa only [NatTrans.comp_app, types_comp_apply, hv] using h.symm
  have hi := eK.homEquiv_comp_uniqueUpToIso_hom r (eK.homEquiv.symm y)
  have hi' : e.homEquiv ((Over.mapPullbackAdj b).homEquiv T J |>.symm
      (eK.homEquiv.symm y ≫ i.hom)) = x := by
    apply (E.app (.op T)).toEquiv.injective
    change r.homEquiv (eK.homEquiv.symm y ≫ i.hom) = E.hom.app (.op T) x
    rw [hi, Equiv.apply_symm_apply, hunit]
  have hm := e.homEquiv.injective (hi'.trans (e.homEquiv.apply_symm_apply x).symm)
  exact congrArg (fun a ↦ a.left) hm

end AlgebraicGeometry
