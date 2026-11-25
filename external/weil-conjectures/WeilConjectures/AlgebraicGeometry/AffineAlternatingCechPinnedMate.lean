/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechModel
public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechExchangeResolution
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # The alternating Čech calculation for the pinned derived mate

Source: Stacks Project, Tags 02KH and 08HY; Steps 1--3 of
`lem-pc-affine-alternating-cech-base-change-factorization`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

private theorem mate_factorization
    {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] [Category* C₄]
    (F : C₁ ⥤ C₂) (R : C₃ ⥤ C₄) (L : C₂ ⥤ C₄) (P : C₁ ⥤ C₃)
    {E₀ E₁ : C₁} {S₁ S₂ : C₂} {Y₀ Y₁ Y₂ : C₃} {T₁ T₂ T₃ : C₄}
    (s : E₀ ≅ E₁) (α : S₁ ≅ F.obj E₁) (v : S₁ ≅ S₂)
    (w : T₁ ≅ T₂) (b : T₁ ≅ T₃) (β : T₃ ≅ R.obj Y₁)
    (z : Y₀ ≅ Y₁) (c : Y₀ ≅ Y₂)
    (d₀ : P.obj E₀ ⟶ Y₀) (d₁ : P.obj E₁ ⟶ Y₁)
    (δ : L.obj S₁ ⟶ T₁) (δ' : L.obj S₂ ⟶ T₂)
    (bc₀ : L.obj (F.obj E₀) ⟶ R.obj (P.obj E₀))
    (bc₁ : L.obj (F.obj E₁) ⟶ R.obj (P.obj E₁))
    (hn : L.map (F.map s.hom) ≫ bc₁ = bc₀ ≫ R.map (P.map s.hom))
    (hp : P.map s.hom ≫ d₁ = d₀ ≫ z.hom)
    (hu : L.map α.hom ≫ bc₁ ≫ R.map d₁ = δ ≫ b.hom ≫ β.hom)
    (hg : L.map v.hom ≫ δ' = δ ≫ w.hom) :
    bc₀ ≫ R.map (d₀ ≫ c.hom) =
      L.map (F.mapIso s ≪≫ α.symm ≪≫ v).hom ≫ δ' ≫
        (w.symm ≪≫ b ≪≫ β ≪≫ R.mapIso z.symm ≪≫ R.mapIso c).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% hg]
  simp only [w.hom_inv_id_assoc]
  rw [← reassoc_of% hu]
  simp only [← L.map_comp_assoc, α.inv_hom_id, Category.comp_id]
  rw [reassoc_of% hn, ← R.map_comp_assoc, hp, R.map_comp]
  simp

private theorem pinnedBaseChange_naturality
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g) {E E' : schemeDerivedCategory X} (a : E ⟶ E') :
    (derivedPullback g).map ((schemeDerivedDirectImage f).map a) ≫
        schemeDerivedBaseChangeMap f f' g p h E' =
      schemeDerivedBaseChangeMap f f' g p h E ≫
        (schemeDerivedDirectImage f').map ((derivedPullback p).map a) := by
  classical
  let δ {V W : Scheme.{u}} (k : V ⟶ W) :=
    (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) k
  let c {V W Z : Scheme.{u}} (k : V ⟶ W) (l : W ⟶ Z) :=
    (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))) k l
  let adj (k : X ⟶ S) := Classical.choose (exists_schemeDerivedAdjunction k
    (hAdd := (Classical.choose exists_derivedPullbackComposition.{u, w}) k)
    (δ k) ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) k))
  let adj' := Classical.choose (exists_schemeDerivedAdjunction f'
    (hAdd := (Classical.choose exists_derivedPullbackComposition.{u, w}) f')
    (δ f') ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) f'))
  let τ : derivedPullback (f' ≫ g) ⟶ derivedPullback (p ≫ f) :=
    (eqToIso (congrArg (fun k ↦ derivedPullback k) h.symm)).hom
  let σ : schemeDerivedDirectImage f ⋙ derivedPullback g ⋙ derivedPullback f' ⟶
      derivedPullback p :=
    Functor.whiskerLeft (schemeDerivedDirectImage f) ((c f' g).hom ≫ τ ≫ (c p f).inv) ≫
      (Functor.associator (schemeDerivedDirectImage f) (derivedPullback f)
        (derivedPullback p)).inv ≫
      Functor.whiskerRight (adj f).counit (derivedPullback p)
  have hx (K : schemeDerivedCategory X) :
      schemeDerivedBaseChangeMap f f' g p h K = adj'.homEquiv _ _ (σ.app K) := by
    unfold schemeDerivedBaseChangeMap
    congr 1
    simp only [σ, τ, adj, δ, c, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp,
      Functor.comp_obj, Category.assoc]
    simp only [eqToIso.hom, eqToHom_app]
  rw [hx, hx]
  exact adj'.homEquiv_naturality_left_square _ _ _ _ (σ.naturality a)

-- Comparing the scheme-module and ringed-space category instances needs this budget.
/-- Compute the mate using precisely the family of counits that defines the
canonical derived composition and adjunction comparisons. This lemma makes no
assertion about a comparison supplied by a caller or a different counit.
Source: Stacks Project, Tags 02KH and 08HY; Steps 1--3 of
`lem-pc-affine-alternating-cech-base-change-factorization`.
(blueprint: lem-pc-affine-alternating-cech-pinned-mate).

Proof: Form the augmented increasing-tuple sheaf Čech complex. On each cover member
insert its index, sort with the permutation sign, and set repeated indices to zero;
the alternating face cancellation gives a contraction. Every intersection is affine
because f is separated over an affine base. The open pushforward of the restricted
quasi-coherent module is f_*-acyclic, so the acyclic resolution comparison identifies
Rf_*G[0] with the explicit sheafified section complex, giving e. Perform the same
construction on the pulled-back cover to compute the target direct image. On each
intersection the affine section-pullback isomorphism sends s tensor b to b times
the pulled-back section s. It commutes with restrictions and with the signed face
sums. Tensor commutes with the finite products in each degree, giving a complex
isomorphism after ordinary g-pullback. Compose its localization with the target
acyclic-resolution comparison to obtain t. Transpose the mate under the pinned
derived adjunction for the base-changed morphism. Evaluate its unit and counit on
the Čech augmentation; the naturality and triangle identities cancel the units.
The remaining maps on every intersection are the pure-tensor maps just described.
The pinned composition comparisons are defined by the same derived counits, so
the transposed equality descends to the displayed equality. There is no need to
invert the counit on K and no flatness hypothesis. An empty cover forces X empty,
and the same construction uses the zero complexes. -/
theorem affineAlternatingCech_pinned_mate
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {A B : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    [QuasiCompact f] [IsSeparated f] (g : Spec B ⟶ Spec A)
    {r : ℕ} (U : Fin r → X.Opens) (hU : iSup U = ⊤)
    (haffine : ∀ i, IsAffineOpen (U i))
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback (pullback.fst f g)).Additive]
    (G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G] :
    ∃ (e : (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≅
        DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (affineAlternatingCechModel f U G)))
        (t : DerivedCategory.Qh.obj (((show
          SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace) ⥤
          SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace) from
          Scheme.Modules.tensorPullback g).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (affineAlternatingCechModel f U G))) ≅
          (schemeDerivedDirectImage (pullback.snd f g)).obj ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj
              ((Scheme.Modules.tensorPullback (pullback.fst f g)).obj G))),
      schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
          pullback.condition ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
        (schemeDerivedDirectImage (pullback.snd f g)).map
          (cast (by rfl) (((Classical.choose (Classical.choose_spec
              exists_derivedPullbackComposition.{u, w})) (pullback.fst f g)).app
            ((HomotopyCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
            DerivedCategory.Qh.map
              ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
                ((HomologicalComplex.singleMapHomologicalComplex
                  (Scheme.Modules.tensorPullback (pullback.fst f g))
                  (ComplexShape.up ℤ) 0).hom.app G)))) =
          (derivedPullback g).map e.hom ≫
            ((Classical.choose (Classical.choose_spec
              exists_derivedPullbackComposition.{u, w})) g).app
              ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
              (affineAlternatingCechModel f U G)) ≫ t.hom := by
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  have hres := exists_affineAlternatingCech_exchange_resolution.{u, w} f g U hU haffine G
  rcases hres with ⟨D, a, q, ha, hpa, hα, hβ, hb⟩
  let F := schemeDerivedDirectImage f
  let R := schemeDerivedDirectImage (pullback.snd f g)
  let L := derivedPullback g
  let P := derivedPullback (pullback.fst f g)
  let Fh := (Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ)
  let Gh := (Scheme.Modules.tensorPullback g).mapHomotopyCategory (ComplexShape.up ℤ)
  let Ph := (Scheme.Modules.tensorPullback (pullback.fst f g)).mapHomotopyCategory
    (ComplexShape.up ℤ)
  let QX := DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let QS := DerivedCategory.Qh
    (C := SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace))
  let QT := DerivedCategory.Qh
    (C := SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace))
  let QY := DerivedCategory.Qh
    (C := SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace))
  let M := (HomotopyCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G
  let δg := (Classical.choose (Classical.choose_spec
    exists_derivedPullbackComposition.{u, w})) g
  let δp := (Classical.choose (Classical.choose_spec
    exists_derivedPullbackComposition.{u, w})) (pullback.fst f g)
  let α := (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app D
  let β := (RingedSpace.moduleDirectImage
    (pullback.snd f g).toLRSHom.toShHom).rightDerivedFunctorUnit.app (Ph.obj D)
  let b := QT.map ((moduleHomotopyBaseChange f (pullback.snd f g) g (pullback.fst f g)
    pullback.condition).app D)
  have : IsIso (QX.map a) := ha
  have : IsIso (QY.map (Ph.map a)) := hpa
  have : IsIso α := hα
  have : IsIso β := hβ
  have : IsIso b := hb
  let sh := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
    ((HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.tensorPullback (pullback.fst f g))
      (ComplexShape.up ℤ) 0).app G)
  let e := F.mapIso (asIso (QX.map a)) ≪≫ (asIso α).symm ≪≫ QS.mapIso q
  let t := (QT.mapIso (Gh.mapIso q)).symm ≪≫ asIso b ≪≫ asIso β ≪≫
    R.mapIso (asIso (QY.map (Ph.map a))).symm ≪≫ R.mapIso (QY.mapIso sh)
  refine ⟨e, t, ?_⟩
  let bc := fun E ↦ schemeDerivedBaseChangeMap f (pullback.snd f g) g
    (pullback.fst f g) pullback.condition E
  have hn := pinnedBaseChange_naturality f (pullback.snd f g) g (pullback.fst f g)
    pullback.condition (QX.map a)
  have hp := δp.naturality a
  have hg := δg.naturality q.hom
  have hu := derivedBaseChange_unit_compatibility f (pullback.snd f g) g
    (pullback.fst f g) pullback.condition D
  change L.map α ≫ bc (QX.obj D) ≫ R.map (δp.app D) =
    δg.app (Fh.obj D) ≫ b ≫ β at hu
  change P.map (QX.map a) ≫ δp.app D = δp.app M ≫ QY.map (Ph.map a) at hp
  change L.map (QS.map q.hom) ≫ δg.app _ =
    δg.app (Fh.obj D) ≫ QT.map (Gh.map q.hom) at hg
  change L.map (F.map (QX.map a)) ≫ bc (QX.obj D) =
    bc (QX.obj M) ≫ R.map (P.map (QX.map a)) at hn
  change bc (QX.obj M) ≫ R.map (δp.app M ≫ QY.map sh.hom) =
    L.map e.hom ≫ δg.app _ ≫ t.hom
  exact mate_factorization F R L P (asIso (QX.map a)) (asIso α) (QS.mapIso q)
    (QT.mapIso (Gh.mapIso q)) (asIso b) (asIso β) (asIso (QY.map (Ph.map a)))
    (QY.mapIso sh) (δp.app M) (δp.app D) (δg.app (Fh.obj D)) (δg.app _)
    (bc (QX.obj M)) (bc (QX.obj D)) hn hp hu hg

end AlgebraicGeometry
