/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomologyEvaluationDefinitions
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.AlgebraicGeometry.TensorPullbackKFlatQuasiIso
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # Local tensor comparison of augmented K-flat resolutions

Source: Stacks Project, Tag 06YJ, independence of K-flat representatives;
Tag 06YI, derived pullback and its compatibility with restriction.
(blueprint: new-s1-local-kflat-tensor-roof). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private noncomputable def tensorRestrictIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] :
    Scheme.Modules.tensorPullback f ≅ Scheme.Modules.restrictFunctor f :=
  (Scheme.Modules.nonempty_tensorPullbackAdjunction f).some.leftAdjointUniq
    (Scheme.Modules.restrictAdjunction f)

private theorem tensorAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.tensorPullback f).Additive := by
  let : (Scheme.Modules.tensorPullback f).IsLeftAdjoint :=
    ⟨_, Scheme.Modules.nonempty_tensorPullbackAdjunction f⟩
  exact CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
    (by rw [CategoryTheory.rightExactFunctor_iff]; infer_instance)

/-- Two resolutions of the same complex on U have a common quasi-isomorphism
roof after tensor pullback and restriction to V intersect i^{-1}(U).

Source: Stacks Project, Tag 06YJ, proof of independence of K-flat representatives,
and Tag 06YI, composition of derived pullbacks, applied to open restriction.
(blueprint: new-s1-local-kflat-tensor-roof).

Proof: Write F for restriction to U. The supplied augmentations a and b identify
F(P) and F(K) with the same object F(S) in D(U), and both sources are K-flat.
Apply `DerivedCategory.right_fac` to this isomorphism to obtain actual chain
maps from a common vertex. Its first map is a quasi-isomorphism by construction;
the second is one because its image in D(U) is an isomorphism. Replace the
vertex by a K-flat resolution and compose with both maps. The maps out of this new vertex
are quasi-isomorphisms between K-flat complexes. Tag 06YJ shows that tensor
pullback along the restricted morphism preserves both maps: exact inverse
image preserves the quasi-isomorphisms and K-flatness, and tensor with the new
structure sheaf preserves quasi-isomorphisms between K-flat complexes.
Restrict this roof to V intersect i^{-1}(U) and then to the over site; those
restrictions are exact and hence preserve quasi-isomorphisms. The termwise
restriction/base-change isomorphisms identify its two ends with G(P) and G(K).
Compose the roof maps with these isomorphisms to get the claimed q and p.
No immersion, affine, regularity, boundedness, freeness or zero-differential assumption is
needed. The vertex is chosen after both augmentations are supplied. In
particular K=0 is permitted only if F(S) is acyclic, because b must be a
quasi-isomorphism. Empty opens give the zero roof. -/
theorem exists_local_kflat_tensor_roof
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [(Scheme.Modules.tensorPullback i).Additive]
    (V : Z.Opens) (U : Y.Opens) (P K S : CochainComplex Y.Modules ℤ) :
    let F := (Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)
    let G := (Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ) ⋙
      moduleOpenOverComplexFunctor Z V (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U))
    ∀ (a : F.obj P ⟶ F.obj S) (b : F.obj K ⟶ F.obj S),
      CochainComplex.IsKFlatTensorResolution (R := U.toScheme.sheaf) a →
      CochainComplex.IsKFlatTensorResolution (R := U.toScheme.sheaf) b →
      ∃ (L : CochainComplex
          (SheafOfModules (V.toScheme.ringCatSheaf.over (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U)))) ℤ)
        (q : L ⟶ G.obj P) (p : L ⟶ G.obj K), QuasiIso q ∧ QuasiIso p := by
  classical
  dsimp only
  intro a b ha hb
  let F := (Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)
  let W := V.ι ⁻¹ᵁ (i ⁻¹ᵁ U)
  let g : W.toScheme ⟶ U.toScheme := (V.ι ≫ i) ∣_ U
  let E := Scheme.Modules.overEquiv W
  have : (Scheme.Modules.tensorPullback g).Additive := tensorAdditive g
  have : PreservesBinaryBiproducts E.inverse :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : E.inverse.Additive := Functor.additive_of_preservesBinaryBiproducts _
  let H := (Scheme.Modules.tensorPullback g ⋙ E.inverse).mapHomologicalComplex (.up ℤ)
  let G := (Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ) ⋙
    moduleOpenOverComplexFunctor Z V W
  have : (Scheme.Modules.restrictFunctor V.ι ⋙
      SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).PreservesZeroMorphisms :=
    moduleOpenOver_preservesZeroMorphisms Z V W
  -- Pullback on W factors through U; compare the two composite left adjoints.
  have e : F ⋙ H ≅ G := by
    have e1 : Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.tensorPullback g ≅
        Scheme.Modules.tensorPullback i ⋙ Scheme.Modules.restrictFunctor V.ι ⋙
          Scheme.Modules.restrictFunctor W.ι :=
      Functor.isoWhiskerRight (tensorRestrictIso U.ι).symm _ ≪≫
        (Scheme.Modules.nonempty_tensorPullbackComp g U.ι).some.symm ≪≫
        eqToIso (congrArg Scheme.Modules.tensorPullback
          (morphismRestrict_ι (V.ι ≫ i) U)) ≪≫
        (Scheme.Modules.nonempty_tensorPullbackComp W.ι (V.ι ≫ i)).some ≪≫
        Functor.isoWhiskerRight
          (Scheme.Modules.nonempty_tensorPullbackComp V.ι i).some _ ≪≫
        Functor.isoWhiskerLeft _
          (Functor.isoWhiskerRight (tensorRestrictIso V.ι) _ ≪≫
            Functor.isoWhiskerLeft _ (tensorRestrictIso W.ι))
    have e2 : Scheme.Modules.restrictFunctor U.ι ⋙
          (Scheme.Modules.tensorPullback g ⋙ E.inverse) ≅
        Scheme.Modules.tensorPullback i ⋙
          (Scheme.Modules.restrictFunctor V.ι ⋙ SheafOfModules.overFunctor
            V.toScheme.ringCatSheaf W) :=
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e1 _ ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
          (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
            (Scheme.Modules.overFunctorEquiv W).isoCompInverse.symm)
    exact NatIso.mapHomologicalComplex e2 (.up ℤ)
  -- First form the common roof in D(U), then make its vertex K-flat.
  let := HasDerivedCategory.standard U.toScheme.Modules
  have : QuasiIso a := ha.1
  have : QuasiIso b := hb.1
  let f := DerivedCategory.Q.map a ≫ inv (DerivedCategory.Q.map b)
  have : IsIso f := by dsimp [f]; infer_instance
  obtain ⟨T, s, hs, t, ht⟩ := DerivedCategory.right_fac f
  have : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).mp hs
  have : IsIso (DerivedCategory.Q.map t) := by
    have h : DerivedCategory.Q.map t = DerivedCategory.Q.map s ≫ f := by
      rw [ht]
      simp
    rw [h]
    infer_instance
  have : QuasiIso t := (DerivedCategory.isIso_Q_map_iff_quasiIso _ t).mp inferInstance
  obtain ⟨R, r, hR, _, hr, _⟩ := CochainComplex.exists_isKFlatResolution T
  have : QuasiIso r := hr
  -- Tensor pullback preserves these maps; the over-site equivalence is exact.
  have hpres {A B : CochainComplex U.toScheme.Modules ℤ} (c : A ⟶ B)
      (hA : CochainComplex.IsKFlatTensor (R := U.toScheme.sheaf) A)
      (hB : CochainComplex.IsKFlatTensor (R := U.toScheme.sheaf) B) (hc : QuasiIso c) :
      QuasiIso (H.map c) := by
    have := tensorPullback_quasiIso_of_isKFlat g c hA hB hc
    change QuasiIso ((E.inverse.mapHomologicalComplex (.up ℤ)).map
      (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).map c))
    infer_instance
  have : QuasiIso (H.map (r ≫ s)) := hpres (r ≫ s) hR ha.2 inferInstance
  have : QuasiIso (H.map (r ≫ t)) := hpres (r ≫ t) hR hb.2 inferInstance
  exact ⟨H.obj R, H.map (r ≫ s) ≫ (e.app P).hom,
    H.map (r ≫ t) ≫ (e.app K).hom, inferInstance, inferInstance⟩

end AlgebraicGeometry
