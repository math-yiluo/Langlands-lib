/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import WeilConjectures.Algebra.Homology.AffineBaseChangeSourceModel
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh

/-! # Cohomology coordinates for affine derived base change

Source: Stacks Project, Tag 0DJ8, affine proof and equation-bc.
(blueprint: lem-pc-affine-base-change-cohomology-model).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem affine_stalkComparison_normalized
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    {K : schemeDerivedCategory X} {K' : schemeDerivedCategory X'}
    {φ : (derivedPullback g').obj K ⟶ K'}
    (c : SingleComplexBaseChange.Coordinates g' K K' φ) (p : X') (i : ℤ) :
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) i
    let st := RingedSpace.moduleStalkFunctor X'.toRingedSpace p
    SingleComplexBaseChange.stalkComparison f f' g g' sq c p i ≫
        (affineRepresentativeStalkIso X' p c.N i).inv ≫ st.map (H.map c.e'.hom) =
      affineBaseChangeIntoPullback f f' g g' sq K c.P c.e c.counit_isIso p i ≫
        st.map (H.map φ) := by
  let := SingleComplexBaseChange.leftAlgebra f g' p
  let := SingleComplexBaseChange.rightAlgebra f f' g g' sq p
  let := (SingleComplexBaseChange.tensorMap f f' g g' sq p).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' p))
  let := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' p))
  have := c.counit_isIso
  dsimp only
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) i
  let st := RingedSpace.moduleStalkFunctor X'.toRingedSpace p
  let T := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj c.P
  have ht : HomologicalComplex.homologyMap
      (((RingedSpace.moduleStalkFunctor X'.toRingedSpace p).mapHomologicalComplex
        (.up ℤ)).map c.t) i ≫ (affineRepresentativeStalkIso X' p c.N i).inv =
      (affineRepresentativeStalkIso X' p T i).inv ≫ st.map (H.map (DerivedCategory.Q.map c.t)) := by
    apply (cancel_epi (affineRepresentativeStalkIso X' p T i).hom).mp
    rw [← Category.assoc, ← affineRepresentativeStalkIso_naturality X' p c.t i]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
    rfl
  have hrep := c.represents
  have hrep' : (DerivedCategory.Q
      (C := SheafOfModules.{u} (moduleRings X'.toRingedSpace))).map c.t ≫ c.e'.hom =
      inv ((SingleComplexBaseChange.counit g').app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj c.P)) ≫
          (derivedPullback g').map c.e.hom ≫ φ := by
    simp only [cast_eq] at hrep
    rw [← hrep]
    erw [IsIso.inv_hom_id_assoc]
  let : HasDerivedCategory.{w} X'.Modules :=
    inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X'.toRingedSpace)))
  have htransport :
      (DerivedCategory.quotientCompQhIso.{w} _).inv.app T ≫
        inv ((SingleComplexBaseChange.counit g').app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj c.P)) ≫
        (derivedPullback g').map ((DerivedCategory.quotientCompQhIso _).hom.app c.P ≫ c.e.hom) =
      inv ((SingleComplexBaseChange.counit g').app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj c.P)) ≫
        (derivedPullback g').map c.e.hom := by
    simp only [DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso,
      Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
    repeat erw [Category.id_comp]
  dsimp only [affineBaseChangeIntoPullback]
  erw [htransport]
  simp only [SingleComplexBaseChange.stalkComparison, Category.assoc, Functor.map_comp]
  dsimp only [st, H, T] at ht
  rw [reassoc_of% ht]
  have hrepmap := congrArg (fun z => st.map (H.map z)) hrep'
  simp only [Functor.map_comp] at hrepmap
  dsimp only [st, H] at hrepmap
  rw [hrepmap]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The degree-i affine module comparison and its prime localizations, without any
invertibility hypothesis. Source: Stacks Project, perfect.tex, Tag 0DJ8, affine
proof, equation-bc and the displayed localization identity.
(blueprint: lem-pc-affine-base-change-cohomology-model).

Proof: first apply exists_affineBaseChangeSourceModel to K and the supplied
K-flat representative c.P, with target the canonical pullback Lg'^*K. This provides
U, its map a0 to global sections of pullback cohomology, its source isomorphism,
a natural affine direct-image cohomology isomorphism d, and the localized source
square. Derived pullback preserves quasi-coherent cohomology. Set V to the actual
global sections of H^i(K') and a to a0 followed by the map on global sections
induced by phi. Set eV to d at K'. Naturality of d and functoriality of H give the
global square. The canonical affineDerivedCohomologyStalkIso identifies V_p with
the stalk of H^i(K'). Compose it with the stalk of H^i(c.e') inverse and the exact
stalk/representative isomorphism to obtain lV. Localization of global sections is
natural, as proved in affineDerivedCohomologyStalkIso_naturality. Exactness of
stalks gives naturality of affineRepresentativeStalkIso for c.t. The represents
equation for c and cancellation of its invertible counit prove
stalkComparison followed by the target normalization equals the comparison into
pullback followed by the stalk of H^i(phi). Apply this equation to lU(x), use the
localized source square and localization of composition, and cancel the target
normalization isomorphism. This proves the local equality for the supplied
coordinates, without selecting different coordinates or assuming any comparison
is invertible. -/
theorem exists_affineBaseChangeCohomologyModel
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    (φf : R →+* A) (φg : R →+* R') (φg' : A →+* A') (φf' : R' →+* A')
    (sq : IsPullback (Spec.map (CommRingCat.ofHom φg')) (Spec.map (CommRingCat.ofHom φf'))
      (Spec.map (CommRingCat.ofHom φf)) (Spec.map (CommRingCat.ofHom φg)))
    (K : schemeDerivedCategory (Spec (.of A)))
    (hK : schemeDerivedQCohProperty (Spec (.of A)) K)
    (K' : schemeDerivedCategory (Spec (.of A')))
    (hK' : schemeDerivedQCohProperty (Spec (.of A')) K')
    (φ : (derivedPullback (Spec.map (CommRingCat.ofHom φg'))).obj K ⟶ K')
    (c : SingleComplexBaseChange.Coordinates (Spec.map (CommRingCat.ofHom φg')) K K' φ)
    (i : ℤ) :
    let F := ModuleCat.restrictScalars φf' ⋙ tilde.functor (.of R')
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of R')).toRingedSpace)) i
    let b := schemeDerivedBaseChangeMap (Spec.map (CommRingCat.ofHom φf))
      (Spec.map (CommRingCat.ofHom φf')) (Spec.map (CommRingCat.ofHom φg))
      (Spec.map (CommRingCat.ofHom φg')) sq.w K ≫
      (schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φf'))).map φ
    ∃ (U V : ModuleCat.{u} A') (a : U ⟶ V)
      (eU : F.obj U ≅ H.obj ((derivedPullback (Spec.map (CommRingCat.ofHom φg))).obj
        ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φf))).obj K)))
      (eV : F.obj V ≅ H.obj
        ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φf'))).obj K')),
      eU.hom ≫ H.map b = F.map a ≫ eV.hom ∧
      ∀ p : PrimeSpectrum A',
        let t := SingleComplexBaseChange.stalkComparison
          (Spec.map (CommRingCat.ofHom φf)) (Spec.map (CommRingCat.ofHom φf'))
          (Spec.map (CommRingCat.ofHom φg)) (Spec.map (CommRingCat.ofHom φg'))
          sq c p i
        ∃ (lU : LocalizedModule p.asIdeal.primeCompl U ≃+ (Arrow.mk t).left)
          (lV : LocalizedModule p.asIdeal.primeCompl V ≃+ (Arrow.mk t).right),
          ∀ x, lV (LocalizedModule.map p.asIdeal.primeCompl a.hom x) = t (lU x) := by
  classical
  dsimp only
  let g' := Spec.map (CommRingCat.ofHom φg')
  let L : schemeDerivedQCohCategory (Spec (.of A')) :=
    ⟨(derivedPullback g').obj K, (derivedPullback_tensor_preserve_QCoh g').1 K hK⟩
  let N : schemeDerivedQCohCategory (Spec (.of A')) := ⟨K', hK'⟩
  let v : L ⟶ N := ⟨φ⟩
  let T := affineDerivedCohomologyModules A' i
  let F := ModuleCat.restrictScalars φf' ⋙ tilde.functor (.of R')
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of R')).toRingedSpace)) i
  obtain ⟨d, U, a, eU, ha, hl⟩ := exists_affineBaseChangeSourceModel
    R A R' A' φf φg φg' φf' sq K hK L.property c.P c.isKFlat c.e c.counit_isIso i
  refine ⟨U, T.obj N, a ≫ T.map v, eU, d.app N, ?_, ?_⟩
  · change eU.hom ≫ H.map (_ ≫ _) = F.map (a ≫ T.map v) ≫ d.hom.app N
    rw [H.map_comp, ← Category.assoc, ha, Category.assoc, F.map_comp]
    have hd := d.hom.naturality v
    change F.map (T.map v) ≫ d.hom.app N =
      d.hom.app L ≫ H.map ((schemeDerivedDirectImage
        (Spec.map (CommRingCat.ofHom φf'))).map φ) at hd
    simpa only [Category.assoc] using
      (congrArg (fun z => F.map a ≫ z) hd).symm
  · intro p
    obtain ⟨lU, hlU⟩ := hl p
    let H' := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace)) i
    let st := RingedSpace.moduleStalkFunctor (Spec (.of A')).toRingedSpace p
    let q := st.mapIso (H'.mapIso c.e')
    let e := (affineRepresentativeStalkIso (Spec (.of A')) p c.N i).symm ≪≫ q
    let lV := (affineDerivedCohomologyStalkIso A' i p N).trans
      e.toLinearEquiv.symm.toAddEquiv
    refine ⟨lU, lV, ?_⟩
    intro x
    apply e.toLinearEquiv.injective
    have hloc : LocalizedModule.map p.asIdeal.primeCompl (a ≫ T.map v).hom x =
        LocalizedModule.map p.asIdeal.primeCompl (T.map v).hom
          (LocalizedModule.map p.asIdeal.primeCompl a.hom x) := by
      change LocalizedModule.map p.asIdeal.primeCompl
        ((T.map v).hom.comp a.hom) x = _
      exact IsLocalizedModule.map_comp' p.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl U)
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (T.obj L))
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (T.obj N)) a.hom (T.map v).hom
        |> fun h => congrArg (fun z => z x) h
    have hn := affine_stalkComparison_normalized
      (Spec.map (CommRingCat.ofHom φf)) (Spec.map (CommRingCat.ofHom φf'))
      (Spec.map (CommRingCat.ofHom φg)) g' sq c p i
    have hn' := congrArg (fun z => z (lU x)) hn
    simp only [ModuleCat.comp_apply] at hn'
    calc
      _ = affineDerivedCohomologyStalkIso A' i p N
          (LocalizedModule.map p.asIdeal.primeCompl (a ≫ T.map v).hom x) :=
        e.toLinearEquiv.apply_symm_apply _
      _ = affineDerivedCohomologyStalkIso A' i p N
          (LocalizedModule.map p.asIdeal.primeCompl (T.map v).hom
            (LocalizedModule.map p.asIdeal.primeCompl a.hom x)) :=
        congrArg (affineDerivedCohomologyStalkIso A' i p N) hloc
      _ = st.map (H'.map φ) (affineDerivedCohomologyStalkIso A' i p L
          (LocalizedModule.map p.asIdeal.primeCompl a.hom x)) :=
        affineDerivedCohomologyStalkIso_naturality A' i p v _
      _ = st.map (H'.map φ) (affineBaseChangeIntoPullback
          (Spec.map (CommRingCat.ofHom φf)) (Spec.map (CommRingCat.ofHom φf'))
          (Spec.map (CommRingCat.ofHom φg)) g' sq K c.P c.e c.counit_isIso p i (lU x)) :=
        congrArg (st.map (H'.map φ)) (hlU x)
      _ = _ := hn'.symm

end AlgebraicGeometry
