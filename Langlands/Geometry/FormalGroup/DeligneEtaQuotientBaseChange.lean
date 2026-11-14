import Langlands.Geometry.FormalGroup.DelignePreDatumBaseChange
import Langlands.Geometry.FormalGroup.DeligneAdmissibility

/-! # Actual eta stalk and Pi quotient comparisons under base change -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

variable {O : Type u} [CommRing O] {X Y : TopCat.{u}}

/-- Pushforward's actual stalk map is natural in module presheaves. -/
theorem moduleStalkPushforward_naturality (f : X ⟶ Y)
    {M N : X.Presheaf (ModuleCat.{u} O)} (g : M ⟶ N) (x : X) :
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) (f x)).map
        ((TopCat.Presheaf.pushforward (ModuleCat.{u} O) f).map g) ≫
        N.stalkPushforward (ModuleCat.{u} O) f x =
      M.stalkPushforward (ModuleCat.{u} O) f x ≫
        (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x).map g := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hx
  rw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ,
    Category.assoc, TopCat.Presheaf.stalkPushforward_germ,
    ← Category.assoc, TopCat.Presheaf.stalkPushforward_germ,
    TopCat.Presheaf.stalkFunctor_map_germ]
  rfl

/-- The presheaf inverse-image stalk isomorphism is natural. -/
theorem moduleStalkPullback_naturality (f : X ⟶ Y)
    {M N : Y.Presheaf (ModuleCat.{u} O)} (g : M ⟶ N) (x : X) :
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) (f x)).map g ≫
        (TopCat.Presheaf.stalkPullbackIso (ModuleCat.{u} O) f N x).hom =
      (TopCat.Presheaf.stalkPullbackIso (ModuleCat.{u} O) f M x).hom ≫
        (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x).map
          ((TopCat.Presheaf.pullback (ModuleCat.{u} O) f).map g) := by
  have h := (TopCat.Presheaf.pullbackPushforwardAdjunction
    (ModuleCat.{u} O) f).unit.naturality g
  simp only [Functor.id_map, Functor.comp_map] at h
  change _ ≫ (_ ≫ _) = (_ ≫ _) ≫ _
  rw [← Category.assoc, ← Functor.map_comp, h,
    Functor.map_comp, Category.assoc, moduleStalkPushforward_naturality,
    ← Category.assoc]

/-- Naturality of the existing comparison for actual sheaf inverse images. -/
theorem inverseImageStalkIso_naturality (f : X ⟶ Y)
    {M N : Y.Sheaf (ModuleCat.{u} O)} (g : M ⟶ N) (x : X) :
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) (f x)).map g.hom ≫
        (inverseImageStalkIso f N x).hom =
      (inverseImageStalkIso f M x).hom ≫
        (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x).map
          ((TopCat.Sheaf.pullback (ModuleCat.{u} O) f).map g).hom := by
  let T := TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x
  let P := TopCat.Presheaf.pullback (ModuleCat.{u} O) f
  let e := TopCat.Sheaf.pullbackIso (ModuleCat.{u} O) f
  have h₁ := moduleStalkPullback_naturality f g.hom x
  have h₂ := congrArg (fun k => T.map k)
    (toSheafify_naturality (Opens.grothendieckTopology X) (P.map g.hom))
  have h₃ : T.map (sheafifyMap (Opens.grothendieckTopology X) (P.map g.hom)) ≫
      T.map (e.inv.app N).hom = T.map (e.inv.app M).hom ≫
        T.map ((TopCat.Sheaf.pullback (ModuleCat.{u} O) f).map g).hom := by
    rw [← T.map_comp, ← T.map_comp]
    exact congrArg (fun k => T.map k.hom) (e.inv.naturality g)
  simp only [Functor.map_comp] at h₂
  dsimp only [inverseImageStalkIso, Iso.trans_hom, asIso_hom,
    Iso.symm_hom, Functor.mapIso_inv]
  change (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) (f x)).map g.hom ≫
      ((TopCat.Presheaf.stalkPullbackIso (ModuleCat.{u} O) f N.obj x).hom ≫
        T.map (toSheafify (Opens.grothendieckTopology X) (P.obj N.obj)) ≫
        T.map (e.inv.app N).hom) =
    ((TopCat.Presheaf.stalkPullbackIso (ModuleCat.{u} O) f M.obj x).hom ≫
        T.map (toSheafify (Opens.grothendieckTopology X) (P.obj M.obj)) ≫
        T.map (e.inv.app M).hom) ≫
      T.map ((TopCat.Sheaf.pullback (ModuleCat.{u} O) f).map g).hom
  calc
    _ = (TopCat.Presheaf.stalkPullbackIso (ModuleCat.{u} O) f M.obj x).hom ≫
        (T.map (P.map g.hom) ≫
          T.map (toSheafify (Opens.grothendieckTopology X) (P.obj N.obj))) ≫
        T.map (e.inv.app N).hom := by
      rw [← Category.assoc, ← Category.assoc, h₁]
      simp only [Category.assoc]
      rfl
    _ = (TopCat.Presheaf.stalkPullbackIso (ModuleCat.{u} O) f M.obj x).hom ≫
        (T.map (toSheafify (Opens.grothendieckTopology X) (P.obj M.obj)) ≫
          T.map (sheafifyMap (Opens.grothendieckTopology X) (P.map g.hom))) ≫
        T.map (e.inv.app N).hom := by rw [h₂]
    _ = _ := by
      simp only [Category.assoc]
      rw [h₃]

variable {d : ℕ} [NeZero d] {π : O}
  {F : Type u} [Field F] [Algebra O F] {S S' : Scheme.{u}}
  {φ : O →+* Γ(S, ⊤)}

namespace SheafPreDatum

variable (D : SheafPreDatum d π F φ) (f : S' ⟶ S)

/-- The original total eta stalk is the actual total eta stalk after base change. -/
def etaStalkPullbackIso (x : S') :
    D.etaStalk (f x) ≅ (D.pullback f).etaStalk x :=
  inverseImageStalkIso f.base
      (latticeScalarSheaf d π (S : TopCat) D.eta.lattice.sheaf) x ≪≫
    ((sheafToPresheaf (Opens.grothendieckTopology (S' : TopCat)) (ModuleCat.{u} O)) ⋙
      TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x).mapIso
        (inverseImageLatticeScalarIso f.base D.eta.lattice.sheaf)

/-- The actual total-stalk comparison intertwines Pi. -/
theorem etaStalkPullbackIso_pi (x : S') (e : D.etaStalk (f x)) :
    (D.etaStalkPullbackIso f x).hom (D.etaStalkPi (f x) e) =
      (D.pullback f).etaStalkPi x ((D.etaStalkPullbackIso f x).hom e) := by
  have h₂ := congrArg
    (fun k => (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x).map k.hom)
    (inverseImageLatticeScalarIso_pi f.base D.eta.lattice.sheaf)
  change (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x).map
      (((TopCat.Sheaf.pullback (ModuleCat.{u} O) f.base).map
        (latticePi d π (S : TopCat) D.eta.lattice.sheaf)).hom ≫
          (inverseImageLatticeScalarIso f.base D.eta.lattice.sheaf).hom.hom) =
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x).map
      ((inverseImageLatticeScalarIso f.base D.eta.lattice.sheaf).hom.hom ≫
        (latticePi d π (S' : TopCat)
          ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f.base).obj
            D.eta.lattice.sheaf)).hom) at h₂
  simp only [Functor.map_comp] at h₂
  have h : ModuleCat.ofHom (D.etaStalkPi (f x)) ≫ (D.etaStalkPullbackIso f x).hom =
      (D.etaStalkPullbackIso f x).hom ≫
        ModuleCat.ofHom ((D.pullback f).etaStalkPi x) := by
    dsimp only [etaStalkPi, etaStalkPullbackIso, Iso.trans_hom,
      Functor.mapIso_hom, Functor.comp_map]
    simp only [ModuleCat.ofHom_hom]
    rw [← Category.assoc, inverseImageStalkIso_naturality, Category.assoc]
    exact congrArg (fun k => (inverseImageStalkIso f.base
      (latticeScalarSheaf d π (S : TopCat) D.eta.lattice.sheaf) x).hom ≫ k) h₂
  exact congrArg (fun k => k e) h

/-- Pi's actual range is transported to Pi's actual range under the stalk comparison. -/
theorem etaStalkPullbackIso_range (x : S') :
    (LinearMap.range (D.etaStalkPi (f x))).map
        (D.etaStalkPullbackIso f x).toLinearEquiv.toLinearMap =
      LinearMap.range ((D.pullback f).etaStalkPi x) := by
  ext y
  constructor
  · rintro ⟨_, ⟨e, rfl⟩, rfl⟩
    exact ⟨(D.etaStalkPullbackIso f x).hom e,
      (D.etaStalkPullbackIso_pi f x e).symm⟩
  · rintro ⟨e, rfl⟩
    obtain ⟨e, rfl⟩ := (D.etaStalkPullbackIso f x).toLinearEquiv.surjective e
    exact ⟨D.etaStalkPi (f x) e, ⟨e, rfl⟩, D.etaStalkPullbackIso_pi f x e⟩

/-- The actual total integral eta/Pi stalk quotient is unchanged under base change. -/
def etaPiQuotientPullbackEquiv (x : S') :
    D.etaPiQuotient (f x) ≃ₗ[O] (D.pullback f).etaPiQuotient x :=
  Submodule.Quotient.equiv _ _ (D.etaStalkPullbackIso f x).toLinearEquiv
    (D.etaStalkPullbackIso_range f x)

/-- The quotient comparison is induced by the actual eta stalk comparison. -/
@[simp]
theorem etaPiQuotientPullbackEquiv_mk (x : S') (e : D.etaStalk (f x)) :
    D.etaPiQuotientPullbackEquiv f x
        ((LinearMap.range (D.etaStalkPi (f x))).mkQ e) =
      (LinearMap.range ((D.pullback f).etaStalkPi x)).mkQ
        ((D.etaStalkPullbackIso f x).hom e) :=
  rfl

end SheafPreDatum

end Langlands.DeligneFormalSpace
