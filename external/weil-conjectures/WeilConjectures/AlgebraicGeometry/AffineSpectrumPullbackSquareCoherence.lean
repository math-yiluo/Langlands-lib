/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDirectImageCoordinates
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedMateEvaluation

/-! # AffineSpectrumPullbackSquareCoherence

Source: Stacks Project, Tags 0D5S and 08HY.
(blueprint: lem-pc-affine-spectrum-pullback-square-coherence).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

private theorem composition_assoc {W X Y Z : Scheme.{u}}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (N : schemeDerivedCategory Z) :
    (derivedPullback a).map ((canonicalDerivedPullbackComposition b c).hom.app N) ≫
      (canonicalDerivedPullbackComposition a (b ≫ c)).hom.app N =
    (canonicalDerivedPullbackComposition a b).hom.app ((derivedPullback c).obj N) ≫
      (canonicalDerivedPullbackComposition (a ≫ b) c).hom.app N ≫
      eqToHom (congrArg (fun q => (derivedPullback q).obj N) (Category.assoc a b c)) := by
  have hc := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))
  have h := (Classical.choose_spec hc.2).2.2 a b c
  change Functor.isoWhiskerRight (canonicalDerivedPullbackComposition b c)
      (derivedPullback a) ≪≫ canonicalDerivedPullbackComposition a (b ≫ c) =
    Functor.associator (derivedPullback c) (derivedPullback b) (derivedPullback a) ≪≫
      Functor.isoWhiskerLeft (derivedPullback c) (canonicalDerivedPullbackComposition a b) ≪≫
      canonicalDerivedPullbackComposition (a ≫ b) c ≪≫
      eqToIso (congrArg (fun q => derivedPullback q) (Category.assoc a b c)) at h
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.associator_hom_app, eqToIso.hom, eqToHom_app, Category.id_comp,
    Category.assoc] using congrArg (fun i => i.hom.app N) h

@[reassoc] private theorem composition_assoc_reverse {W X Y Z : Scheme.{u}}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (N : schemeDerivedCategory Z) :
    (canonicalDerivedPullbackComposition a b).hom.app ((derivedPullback c).obj N) ≫
      (canonicalDerivedPullbackComposition (a ≫ b) c).hom.app N =
    (derivedPullback a).map ((canonicalDerivedPullbackComposition b c).hom.app N) ≫
      (canonicalDerivedPullbackComposition a (b ≫ c)).hom.app N ≫
      eqToHom (congrArg (fun q => (derivedPullback q).obj N) (Category.assoc a b c).symm) := by
  apply (cancel_mono (eqToHom
    (congrArg (fun q => (derivedPullback q).obj N) (Category.assoc a b c)))).1
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using
    (composition_assoc a b c N).symm

@[reassoc] private theorem composition_congr_left {P Q R : Scheme.{u}} (a a' : P ⟶ Q)
    (b : Q ⟶ R) (e : a = a') (N : schemeDerivedCategory R) :
    eqToHom (congrArg (fun q => (derivedPullback q).obj ((derivedPullback b).obj N)) e) ≫
      (canonicalDerivedPullbackComposition a' b).hom.app N =
    (canonicalDerivedPullbackComposition a b).hom.app N ≫
      eqToHom (congrArg (fun q => (derivedPullback q).obj N)
        (congrArg (fun q => q ≫ b) e)) := by
  subst a'
  simp

@[reassoc] private theorem composition_congr_right {P Q R : Scheme.{u}} (a : P ⟶ Q)
    (b b' : Q ⟶ R) (e : b = b') (N : schemeDerivedCategory R) :
    (derivedPullback a).map
        (eqToHom (congrArg (fun q => (derivedPullback q).obj N) e)) ≫
      (canonicalDerivedPullbackComposition a b').hom.app N =
    (canonicalDerivedPullbackComposition a b).hom.app N ≫
      eqToHom (congrArg (fun q => (derivedPullback q).obj N)
        (congrArg (fun q => a ≫ q) e)) := by
  subst b'
  simp

private noncomputable def forward {P Q P₀ Q₀ : Scheme.{u}}
    (a : P ⟶ Q) (a₀ : P₀ ⟶ Q₀) (vP : P ⟶ P₀) (vQ : Q ⟶ Q₀)
    (e : a ≫ vQ = vP ≫ a₀) (N : schemeDerivedCategory Q₀) :
    (derivedPullback a).obj ((derivedPullback vQ).obj N) ⟶
      (derivedPullback vP).obj ((derivedPullback a₀).obj N) :=
  (canonicalDerivedPullbackComposition a vQ).hom.app N ≫
    eqToHom (congrArg (fun q => (derivedPullback q).obj N) e) ≫
    (canonicalDerivedPullbackComposition vP a₀).inv.app N

private theorem forward_comp {P Q R P₀ Q₀ R₀ : Scheme.{u}}
    (a : P ⟶ Q) (b : Q ⟶ R) (a₀ : P₀ ⟶ Q₀) (b₀ : Q₀ ⟶ R₀)
    (vP : P ⟶ P₀) (vQ : Q ⟶ Q₀) (vR : R ⟶ R₀)
    (d : a ≫ vQ = vP ≫ a₀) (e : b ≫ vR = vQ ≫ b₀)
    (t : (a ≫ b) ≫ vR = vP ≫ (a₀ ≫ b₀)) (N : schemeDerivedCategory R₀) :
    (derivedPullback a).map (forward b b₀ vQ vR e N) ≫
        forward a a₀ vP vQ d ((derivedPullback b₀).obj N) ≫
        (derivedPullback vP).map ((canonicalDerivedPullbackComposition a₀ b₀).hom.app N) =
      (canonicalDerivedPullbackComposition a b).hom.app ((derivedPullback vR).obj N) ≫
        forward (a ≫ b) (a₀ ≫ b₀) vP vR t N := by
  apply (cancel_mono ((canonicalDerivedPullbackComposition vP (a₀ ≫ b₀)).hom.app N)).1
  simp only [forward, Functor.map_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [composition_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [composition_congr_left_assoc _ _ _ d N]
  rw [composition_assoc_reverse_assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [composition_congr_right_assoc _ _ _ e N]
  rw [← Category.assoc ((derivedPullback a).map _), composition_assoc]
  simp only [Category.assoc, eqToHom_trans]

private theorem forward_congr {P Q P₀ Q₀ : Scheme.{u}}
    (a a' : P ⟶ Q) (b b' : P₀ ⟶ Q₀) (vP : P ⟶ P₀) (vQ : Q ⟶ Q₀)
    (d : a ≫ vQ = vP ≫ b) (d' : a' ≫ vQ = vP ≫ b')
    (e : a = a') (e₀ : b = b') (N : schemeDerivedCategory Q₀) :
    forward a b vP vQ d N ≫
        (derivedPullback vP).map
          (eqToHom (congrArg (fun q => (derivedPullback q).obj N) e₀)) =
      eqToHom (congrArg (fun q => (derivedPullback q).obj ((derivedPullback vQ).obj N)) e) ≫
        forward a' b' vP vQ d' N := by
  subst a'
  subst b'
  simp

@[reassoc] private theorem square_naturality {P Q P' Q' : Scheme.{u}}
    (a : P ⟶ Q) (a' : P' ⟶ Q') (b : Q' ⟶ Q) (b' : P' ⟶ P)
    (e : b' ≫ a = a' ≫ b) {M N : schemeDerivedCategory Q} (k : M ⟶ N) :
    (derivedPullback a').map ((derivedPullback b).map k) ≫
        canonicalDerivedSquareComparison a a' b b' e N =
      canonicalDerivedSquareComparison a a' b b' e M ≫
        (derivedPullback b').map ((derivedPullback a).map k) := by
  let i := canonicalDerivedPullbackComposition a' b ≪≫
    eqToIso (congrArg (fun q => derivedPullback q) e.symm) ≪≫
    (canonicalDerivedPullbackComposition b' a).symm
  simpa only [i, canonicalDerivedSquareComparison, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, eqToIso.hom, eqToHom_app, Functor.comp_map, Category.assoc] using
    i.hom.naturality k

private theorem forward_iso_app {P Q P₀ Q₀ : Scheme.{u}}
    (a : P ⟶ Q) (a₀ : P₀ ⟶ Q₀) (vP : P ⟶ P₀) (vQ : Q ⟶ Q₀)
    (e : a ≫ vQ = vP ≫ a₀) (N : schemeDerivedCategory Q₀) :
    (canonicalDerivedPullbackComposition a vQ ≪≫
      eqToIso (congrArg (fun q => derivedPullback q) e) ≪≫
      (canonicalDerivedPullbackComposition vP a₀).symm).hom.app N =
      forward a a₀ vP vQ e N := by
  simp only [forward, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app]

private theorem forward_spectrum_iso {P Q : Scheme.{u}} [IsAffine P] [IsAffine Q]
    (a : P ⟶ Q) :
    affineSpectrumForwardPullbackIso a =
      canonicalDerivedPullbackComposition a Q.toSpecΓ ≪≫
        eqToIso (congrArg (fun q => derivedPullback q) (Scheme.toSpecΓ_naturality a)) ≪≫
        (canonicalDerivedPullbackComposition P.toSpecΓ (Spec.map a.appTop)).symm := by
  rfl

private theorem forward_spectrum {P Q : Scheme.{u}} [IsAffine P] [IsAffine Q]
    (a : P ⟶ Q) (N : schemeDerivedCategory (Spec Γ(Q, ⊤))) :
    (affineSpectrumForwardPullbackIso a).hom.app N =
      forward a (Spec.map a.appTop) P.toSpecΓ Q.toSpecΓ
        (Scheme.toSpecΓ_naturality a) N := by
  exact (congrArg (fun i => i.hom.app N) (forward_spectrum_iso a)).trans
    (forward_iso_app a (Spec.map a.appTop) P.toSpecΓ Q.toSpecΓ
      (Scheme.toSpecΓ_naturality a) N)

private theorem forward_square {X X' S S' X₀ X'₀ S₀ S'₀ : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (f₀ : X₀ ⟶ S₀) (f'₀ : X'₀ ⟶ S'₀) (g₀ : S'₀ ⟶ S₀) (g'₀ : X'₀ ⟶ X₀)
    (vX : X ⟶ X₀) (vX' : X' ⟶ X'₀) (vS : S ⟶ S₀) (vS' : S' ⟶ S'₀)
    (df : f ≫ vS = vX ≫ f₀) (df' : f' ≫ vS' = vX' ≫ f'₀)
    (dg : g ≫ vS = vS' ≫ g₀) (dg' : g' ≫ vX = vX' ≫ g'₀)
    (h : g' ≫ f = f' ≫ g)
    (h₀ : g'₀ ≫ f₀ =
      f'₀ ≫ g₀)
    (N : schemeDerivedCategory S₀) :
    (derivedPullback f').map (forward g g₀ vS' vS dg N) ≫
        forward f' f'₀ vX' vS' df'
          ((derivedPullback (g₀)).obj N) ≫
        (derivedPullback vX').map
          (canonicalDerivedSquareComparison (f₀) (f'₀)
            (g₀) (g'₀) h₀ N) =
      canonicalDerivedSquareComparison f f' g g' h ((derivedPullback vS).obj N) ≫
        (derivedPullback g').map (forward f f₀ vX vS df N) ≫
        forward g' g'₀ vX' vX dg'
          ((derivedPullback (f₀)).obj N) := by
  have tL : (f' ≫ g) ≫ vS =
      vX' ≫ (f'₀ ≫ g₀) := by
    rw [Category.assoc, dg, ← Category.assoc,
      df', Category.assoc]
  have tR : (g' ≫ f) ≫ vS =
      vX' ≫ (g'₀ ≫ f₀) := by
    rw [Category.assoc, df, ← Category.assoc,
      dg', Category.assoc]
  have left := forward_comp f' g (f'₀) (g₀)
    vX' vS' vS (df')
    (dg) tL N
  have right := forward_comp g' f (g'₀) (f₀)
    vX' vX vS (dg')
    (df) tR N
  have middle := forward_congr (f' ≫ g) (g' ≫ f)
    (f'₀ ≫ g₀)
    (g'₀ ≫ f₀) vX' vS tL tR h.symm h₀.symm N
  apply (cancel_mono ((derivedPullback vX').map
    ((canonicalDerivedPullbackComposition (g'₀)
      (f₀)).hom.app N))).1
  simp only [canonicalDerivedSquareComparison, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app, Category.comp_id]
  simp only [Functor.map_comp]
  have leftE := congrArg (fun z => z ≫ (derivedPullback vX').map
    (eqToHom (congrArg (fun q => (derivedPullback q).obj N) h₀.symm))) left
  calc
    _ = (canonicalDerivedPullbackComposition f' g).hom.app
        ((derivedPullback vS).obj N) ≫
        forward (f' ≫ g) (f'₀ ≫ g₀)
          vX' vS tL N ≫
        (derivedPullback vX').map
          (eqToHom (congrArg (fun q => (derivedPullback q).obj N) h₀.symm)) := by
      simpa only [Category.assoc] using leftE
    _ = (canonicalDerivedPullbackComposition f' g).hom.app
        ((derivedPullback vS).obj N) ≫
        eqToHom (congrArg (fun q => (derivedPullback q).obj
          ((derivedPullback vS).obj N)) h.symm) ≫
        forward (g' ≫ f) (g'₀ ≫ f₀)
          vX' vS tR N := by rw [middle]
    _ = _ := by
      rw [right]
      simp only [Iso.inv_hom_id_app_assoc]

private theorem spectrum_square {X X' S S' : Scheme.{u}}
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (h₀ : Spec.map g'.appTop ≫ Spec.map f.appTop =
      Spec.map f'.appTop ≫ Spec.map g.appTop)
    (N : schemeDerivedCategory (Spec Γ(S, ⊤))) :
    (derivedPullback f').map ((affineSpectrumForwardPullbackIso g).hom.app N) ≫
        (affineSpectrumForwardPullbackIso f').hom.app
          ((derivedPullback (Spec.map g.appTop)).obj N) ≫
        (derivedPullback X'.toSpecΓ).map
          (canonicalDerivedSquareComparison (Spec.map f.appTop) (Spec.map f'.appTop)
            (Spec.map g.appTop) (Spec.map g'.appTop) h₀ N) =
      canonicalDerivedSquareComparison f f' g g' h ((derivedPullback S.toSpecΓ).obj N) ≫
        (derivedPullback g').map ((affineSpectrumForwardPullbackIso f).hom.app N) ≫
        (affineSpectrumForwardPullbackIso g').hom.app
          ((derivedPullback (Spec.map f.appTop)).obj N) := by
  simp only [forward_spectrum]
  exact forward_square f f' g g'
    (Spec.map f.appTop) (Spec.map f'.appTop) (Spec.map g.appTop) (Spec.map g'.appTop)
    X.toSpecΓ X'.toSpecΓ S.toSpecΓ S'.toSpecΓ
    (Scheme.toSpecΓ_naturality f) (Scheme.toSpecΓ_naturality f')
    (Scheme.toSpecΓ_naturality g) (Scheme.toSpecΓ_naturality g') h h₀ N

/-- The square pullback comparison commutes with forward spectrum coordinates.

Proof: expand q and each forward comparison into c and the equality isomorphisms
for scheme naturality. Naturality of c moves the arbitrary map k to the right;
thus it suffices to compare natural transformations at N. Apply the associativity
law for c to each of the four length-three paths around the commutative prism
whose vertical maps are toSpecGamma. Scheme.toSpecGamma_naturality identifies
its four side faces, and h and h0 identify the bottom and top faces. The equality
isomorphisms are independent of the chosen equality proofs by proof irrelevance.
Cancel adjacent inverse comparisons. Both composites become the comparison for
the same length-three scheme map; hence they agree. No direct image, counit or
base-change mate occurs, and k is arbitrary. Identities and zero objects need
no separate case.
Source: Stacks Project, Tags 0D5S and 08HY.
(blueprint: lem-pc-affine-spectrum-pullback-square-coherence). -/
theorem affineSpectrum_pullback_square_coherence
    {X X' S S' : Scheme.{u}}
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (h0 : Spec.map g'.appTop ≫ Spec.map f.appTop =
      Spec.map f'.appTop ≫ Spec.map g.appTop)
    (M : schemeDerivedCategory S) (N : schemeDerivedCategory (Spec Γ(S, ⊤)))
    (k : M ⟶ (derivedPullback S.toSpecΓ).obj N) :
  (derivedPullback f').map
      ((derivedPullback g).map k ≫ (affineSpectrumForwardPullbackIso g).hom.app N) ≫
      (affineSpectrumForwardPullbackIso f').hom.app
        ((derivedPullback (Spec.map g.appTop)).obj N) ≫
      (derivedPullback X'.toSpecΓ).map
        (canonicalDerivedSquareComparison (Spec.map f.appTop) (Spec.map f'.appTop)
          (Spec.map g.appTop) (Spec.map g'.appTop) h0 N) =
    canonicalDerivedSquareComparison f f' g g' h M ≫
      (derivedPullback g').map ((derivedPullback f).map k) ≫
      (derivedPullback g').map ((affineSpectrumForwardPullbackIso f).hom.app N) ≫
      (affineSpectrumForwardPullbackIso g').hom.app
        ((derivedPullback (Spec.map f.appTop)).obj N) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [spectrum_square, square_naturality_assoc]

end AlgebraicGeometry
