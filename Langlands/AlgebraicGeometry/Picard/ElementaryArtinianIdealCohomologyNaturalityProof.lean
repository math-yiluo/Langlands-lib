import Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealResidueProduct
import Langlands.AlgebraicGeometry.Picard.ElementaryArtinianResidueCoefficient
import Langlands.AlgebraicGeometry.Modules.CanonicalPushforwardCohomology
import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackBaseRing
import Langlands.AlgebraicGeometry.Modules.FieldGlobalFunctionsAlgebra
import Langlands.AlgebraicGeometry.Picard.ArtinianResidueCohomology

/-! # Naturality of elementary Artinian ideal cohomology in residue coordinates -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

section Congr

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)}

/-- The canonical pushforward comparison along equal morphisms. -/
lemma canonicalPushforwardCohomologyMap_congr {f g : Y ⟶ X} (w : f = g)
    (N : Y.left.Modules) (n : ℕ) :
    (relativeCohomology X.hom n).map
        ((Scheme.Modules.pushforwardCongr (congrArg (fun q : Y ⟶ X => q.left) w)).hom.app N) ≫
      canonicalPushforwardCohomologyMap g N n = canonicalPushforwardCohomologyMap f N n := by
  subst w
  have h₁ : (Scheme.Modules.pushforwardCongr (rfl : f.left = f.left)).hom.app N = 𝟙 _ :=
    Scheme.Modules.hom_ext _ _ fun U => by simp
  rw [h₁, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The canonical pushforward comparison is canonical pullback followed by the counit. -/
lemma canonicalPushforwardCohomologyMap_eq_pullback_counit (g : Y ⟶ X)
    (N : Y.left.Modules) (n : ℕ) :
    canonicalPushforwardCohomologyMap g N n =
      relativeCohomologyPullback g ((Scheme.Modules.pushforward g.left).obj N) n ≫
        (relativeCohomology Y.hom n).map
          ((Scheme.Modules.pullbackPushforwardAdjunction g.left).counit.app N) := by
  rw [relativeCohomologyPullback_coefficient, Adjunction.homEquiv_unit,
    Adjunction.right_triangle_components, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

end Congr

section BaseRing

variable {R R' : CommRingCat.{u}} (φ : R ⟶ R') {X Y : Over (Spec R')} (h : Y ⟶ X)

/-- The canonical pushforward comparison commutes with change of the affine base ring. -/
lemma canonicalPushforwardCohomologyMap_overMap (N : Y.left.Modules) (n : ℕ) :
    canonicalPushforwardCohomologyMap ((Over.map (Spec.map φ)).map h) N n ≫
        (relativeCohomologyBaseRingIso φ ((Over.map (Spec.map φ)).obj Y).hom Y.hom rfl n).hom.app
          N =
      (relativeCohomologyBaseRingIso φ ((Over.map (Spec.map φ)).obj X).hom X.hom rfl n).hom.app
          ((Scheme.Modules.pushforward h.left).obj N) ≫
        (ModuleCat.restrictScalars φ.hom).map (canonicalPushforwardCohomologyMap h N n) := by
  have hn := (relativeCohomologyBaseRingIso φ ((Over.map (Spec.map φ)).obj Y).hom Y.hom rfl
    n).hom.naturality ((Scheme.Modules.pullbackPushforwardAdjunction h.left).counit.app N)
  have hp := relativeCohomologyPullback_overMap φ h ((Scheme.Modules.pushforward h.left).obj N) n
  rw [canonicalPushforwardCohomologyMap_eq_pullback_counit,
    canonicalPushforwardCohomologyMap_eq_pullback_counit, Category.assoc]
  dsimp only [Over.map_map_left, Over.map_obj_left] at hn hp ⊢
  erw [hn, reassoc_of% hp]
  rw [Functor.map_comp]
  rfl

end BaseRing

end Langlands.AlgebraicGeometry.Modules.DerivedSections

namespace Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology

open StructureKernelModule Langlands.Scheme.Modules
  Langlands.AlgebraicGeometry.Modules.DerivedSections
  PicardGroupoid.ArtinianResidueCohomology

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) [IsLocalRing S]

/-- The residue ring map `R → K`. -/
abbrev residueRingHom : CommRingCat.of R ⟶ CommRingCat.of (ResidueField S) :=
  CommRingCat.ofHom ((residue S).comp φ)

/-- The actual residue fibre regarded over the source base `Spec R`. -/
abbrev residueOver (X : Over (Spec (CommRingCat.of R))) : Over (Spec (CommRingCat.of R)) :=
  (Over.map (residueBaseMap φ)).obj ((residuePullback φ).obj X)

/-- The residue-fibre inclusion as a morphism over `Spec R`. -/
def residueιOver (X : Over (Spec (CommRingCat.of R))) : residueOver φ X ⟶ X :=
  Over.homMk (residueι φ X) pullback.condition

@[simp]
lemma residueιOver_left (X : Over (Spec (CommRingCat.of R))) :
    (residueιOver φ X).left = residueι φ X := rfl

/-- The residue-fibre square over `Spec R`. -/
lemma residueιOver_naturality {X Y : Over (Spec (CommRingCat.of R))} (f : Y ⟶ X) :
    (Over.map (residueBaseMap φ)).map ((residuePullback φ).map f) ≫ residueιOver φ X =
      residueιOver φ Y ≫ f := by
  ext
  exact residueι_naturality φ f

variable (n : ℕ)

/-- Residue structure cohomology over `R` and the residue base ring isomorphism. -/
abbrev residueBaseRingIso (X : Over (Spec (CommRingCat.of R))) :=
  relativeCohomologyBaseRingIso (residueRingHom φ) (residueOver φ X).hom
    ((residuePullback φ).obj X).hom rfl n

lemma residueι_isClosedImmersion (hφ : Function.Surjective φ)
    (X : Over (Spec (CommRingCat.of R))) : IsClosedImmersion (residueιOver φ X).left := by
  have : IsClosedImmersion (residueBaseMap φ) :=
    IsClosedImmersion.spec_of_surjective _ (residue_surjective.comp hφ)
  change IsClosedImmersion (pullback.fst X.hom (residueBaseMap φ))
  infer_instance

/-- One residue coordinate: canonical closed-immersion comparison, then scalar restriction. -/
def coordinateEquiv (hφ : Function.Surjective φ) (X : Over (Spec (CommRingCat.of R))) :
    (relativeCohomology X.hom n).obj (residueModule φ X) ≃+
      structureCohomology ((residuePullback φ).obj X) n :=
  have := residueι_isClosedImmersion φ hφ X
  haveI := isIso_canonicalPushforwardCohomologyMap_closedImmersion (residueιOver φ X)
    (SheafOfModules.unit ((residuePullback φ).obj X).left.ringCatSheaf) n
  ((asIso (canonicalPushforwardCohomologyMap (residueιOver φ X)
      (SheafOfModules.unit ((residuePullback φ).obj X).left.ringCatSheaf) n)) ≪≫
    (residueBaseRingIso φ n X).app _).toLinearEquiv.toAddEquiv

lemma coordinateEquiv_apply (hφ : Function.Surjective φ) (X : Over (Spec (CommRingCat.of R)))
    (z : (relativeCohomology X.hom n).obj (residueModule φ X)) :
    coordinateEquiv φ n hφ X z =
      ((canonicalPushforwardCohomologyMap (residueιOver φ X)
          (SheafOfModules.unit ((residuePullback φ).obj X).left.ringCatSheaf) n ≫
        (residueBaseRingIso φ n X).hom.app _).hom z : _) := rfl

/-- The coordinate square for one residue coordinate, at the level of morphisms. -/
lemma coordinate_square {X Y : Over (Spec (CommRingCat.of R))} (f : Y ⟶ X) :
    (relativeCohomology X.hom n).map (residueCoefficient φ f) ≫
        canonicalPushforwardCohomologyMap f (residueModule φ Y) n ≫
        canonicalPushforwardCohomologyMap (residueιOver φ Y)
          (SheafOfModules.unit ((residuePullback φ).obj Y).left.ringCatSheaf) n ≫
        (residueBaseRingIso φ n Y).hom.app _ =
      canonicalPushforwardCohomologyMap (residueιOver φ X)
          (SheafOfModules.unit ((residuePullback φ).obj X).left.ringCatSheaf) n ≫
        (residueBaseRingIso φ n X).hom.app _ ≫
        (ModuleCat.restrictScalars (residueRingHom φ).hom).map
          (relativeCohomologyPullback ((residuePullback φ).map f)
              (SheafOfModules.unit ((residuePullback φ).obj X).left.ringCatSheaf) n ≫
            (relativeCohomology ((residuePullback φ).obj Y).hom n).map
              (pullbackUnitIso ((residuePullback φ).map f).left).hom) := by
  let OX := SheafOfModules.unit ((residuePullback φ).obj X).left.ringCatSheaf
  let OY := SheafOfModules.unit ((residuePullback φ).obj Y).left.ringCatSheaf
  let fK := (residuePullback φ).map f
  let fR := (Over.map (residueBaseMap φ)).map fK
  have h₁ : canonicalPushforwardCohomologyMap f (residueModule φ Y) n ≫
      canonicalPushforwardCohomologyMap (residueιOver φ Y) OY n =
      (relativeCohomology X.hom n).map
          ((Scheme.Modules.pushforwardComp (residueι φ Y) f.left).hom.app OY) ≫
        canonicalPushforwardCohomologyMap (residueιOver φ Y ≫ f) OY n :=
    canonicalPushforwardCohomologyMap_comp f (residueιOver φ Y) OY n
  have h₃ : (relativeCohomology X.hom n).map
        ((Scheme.Modules.pushforwardCongr (residueι_naturality φ f)).hom.app OY) ≫
      canonicalPushforwardCohomologyMap (residueιOver φ Y ≫ f) OY n =
      canonicalPushforwardCohomologyMap (fR ≫ residueιOver φ X) OY n :=
    canonicalPushforwardCohomologyMap_congr (residueιOver_naturality φ f) OY n
  have h₄ : (relativeCohomology X.hom n).map
        ((Scheme.Modules.pushforwardComp fK.left (residueι φ X)).hom.app OY) ≫
      canonicalPushforwardCohomologyMap (fR ≫ residueιOver φ X) OY n =
      canonicalPushforwardCohomologyMap (residueιOver φ X)
          ((Scheme.Modules.pushforward fK.left).obj OY) n ≫
        canonicalPushforwardCohomologyMap fR OY n :=
    (canonicalPushforwardCohomologyMap_comp (residueιOver φ X) fR OY n).symm
  have h₅ : (relativeCohomology X.hom n).map
        ((Scheme.Modules.pushforward (residueι φ X)).map (unitToPushforwardUnit fK.left)) ≫
      canonicalPushforwardCohomologyMap (residueιOver φ X)
          ((Scheme.Modules.pushforward fK.left).obj OY) n =
      canonicalPushforwardCohomologyMap (residueιOver φ X) OX n ≫
        (relativeCohomology (residueOver φ X).hom n).map (unitToPushforwardUnit fK.left) :=
    canonicalPushforwardCohomologyMap_naturality (residueιOver φ X) (unitToPushforwardUnit fK.left) n
  have h₆ : canonicalPushforwardCohomologyMap fR OY n ≫ (residueBaseRingIso φ n Y).hom.app OY =
      (residueBaseRingIso φ n X).hom.app ((Scheme.Modules.pushforward fK.left).obj OY) ≫
        (ModuleCat.restrictScalars (residueRingHom φ).hom).map
          (canonicalPushforwardCohomologyMap fK OY n) :=
    canonicalPushforwardCohomologyMap_overMap (residueRingHom φ) fK OY n
  have h₇ := (residueBaseRingIso φ n X).hom.naturality (unitToPushforwardUnit fK.left)
  have h₈ : (relativeCohomology ((residuePullback φ).obj X).hom n).map
        (unitToPushforwardUnit fK.left) ≫ canonicalPushforwardCohomologyMap fK OY n =
      relativeCohomologyPullback fK OX n ≫
        (relativeCohomology ((residuePullback φ).obj Y).hom n).map
          (pullbackUnitIso fK.left).hom := by
    rw [relativeCohomologyPullback_coefficient, Adjunction.homEquiv_unit,
      Langlands.AlgebraicGeometry.Modules.FieldGlobalFunctions.pullbackUnitIso_unit]
  simp only [Functor.comp_map] at h₇
  rw [← h₈]
  simp only [residueCoefficient, Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₁, ← Functor.map_comp_assoc (relativeCohomology X.hom n)
      ((Scheme.Modules.pushforwardComp (residueι φ Y) f.left).inv.app OY),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    reassoc_of% h₃, reassoc_of% h₄, reassoc_of% h₅, h₆, reassoc_of% h₇]

/-- Reindexing functions along an equivalence of index types. -/
def reindexAddEquiv {A : Type*} [AddCommGroup A] {ι κ : Type*} (e : ι ≃ κ) :
    (ι → A) ≃+ (κ → A) where
  toFun v j := v (e.symm j)
  invFun w i := w (e i)
  left_inv v := by funext i; simp
  right_inv w := by funext j; simp
  map_add' _ _ := rfl

@[simp]
lemma reindexAddEquiv_apply {A : Type*} [AddCommGroup A] {ι κ : Type*} (e : ι ≃ κ)
    (v : ι → A) (j : κ) : reindexAddEquiv e v j = v (e.symm j) := rfl

/-- The additive equivalence underlying an isomorphism of modules. -/
def isoAddEquiv {A : Type u} [CommRing A] {M N : ModuleCat.{u} A} (i : M ≅ N) : M ≃+ N where
  toFun x := i.hom.hom x
  invFun y := i.inv.hom y
  left_inv x := by simp
  right_inv y := by simp
  map_add' x y := map_add i.hom.hom x y

@[simp]
lemma isoAddEquiv_apply {A : Type u} [CommRing A] {M N : ModuleCat.{u} A} (i : M ≅ N) (x : M) :
    isoAddEquiv i x = i.hom.hom x := rfl

/-- The finite residue coordinates of actual ideal cohomology. -/
def idealCoordinates (hφ : Function.Surjective φ) (X : Over (Spec (CommRingCat.of R)))
    {ι : Type u} [Finite ι] (eX : ideal φ X ≅ ∏ᶜ fun _ : ι => residueModule φ X)
    {d : ℕ} (eι : ι ≃ Fin d) :
    idealCohomology φ X n ≃+ (Fin d → structureCohomology ((residuePullback φ).obj X) n) :=
  (isoAddEquiv ((relativeCohomology X.hom n).mapIso eX)).trans
    ((isoAddEquiv (finiteProductCohomologyIso X.hom (residueModule φ X) ι n)).trans
      ((AddEquiv.piCongrRight fun _ => coordinateEquiv φ n hφ X).trans (reindexAddEquiv eι)))

lemma idealCoordinates_apply (hφ : Function.Surjective φ) (X : Over (Spec (CommRingCat.of R)))
    {ι : Type u} [Finite ι] (eX : ideal φ X ≅ ∏ᶜ fun _ : ι => residueModule φ X)
    {d : ℕ} (eι : ι ≃ Fin d) (x : idealCohomology φ X n) (j : Fin d) :
    idealCoordinates φ n hφ X eX eι x j =
      coordinateEquiv φ n hφ X (((relativeCohomology X.hom n).map
        (eX.hom ≫ Pi.π (fun _ : ι => residueModule φ X) (eι.symm j))).hom x) := by
  simp only [idealCoordinates, AddEquiv.trans_apply, reindexAddEquiv_apply,
    AddEquiv.piCongrRight_apply, isoAddEquiv_apply, Functor.mapIso_hom]
  have h := finiteProductCohomologyIso_apply X.hom (residueModule φ X) ι n
    (((relativeCohomology X.hom n).map eX.hom).hom x) (eι.symm j)
  rw [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact congrArg (coordinateEquiv φ n hφ X) h

omit [IsLocalRing S] in
lemma idealPull_eq {X Y : Over (Spec (CommRingCat.of R))} (f : Y ⟶ X)
    (k : ideal φ X ⟶ (Scheme.Modules.pushforward f.left).obj (ideal φ Y)) :
    idealPull φ f k n =
      ((relativeCohomology X.hom n).map k ≫
        canonicalPushforwardCohomologyMap f (ideal φ Y) n).hom := by
  unfold idealPull
  rw [relativeCohomologyPullback_coefficient, Equiv.apply_symm_apply]

set_option maxRecDepth 8192 in
/-- Naturality of elementary Artinian ideal cohomology in finite residue coordinates. -/
theorem naturalityStatement : NaturalityStatement.{u} := by
  intro R S _ _ _ _ _ _ φ hφ hker X Y _ _ _ _ n
  obtain ⟨ι, hι, e, he⟩ := exists_idealResidueProductIso φ hφ hker
  have := Fintype.ofFinite ι
  refine ⟨Fintype.card ι, idealCoordinates φ n hφ X (e X) (Fintype.equivFin ι),
    idealCoordinates φ n hφ Y (e Y) (Fintype.equivFin ι), ?_⟩
  intro f k hk x j
  rw [idealCoordinates_apply, idealCoordinates_apply, idealPull_eq]
  have hsq := he X Y f k hk ((Fintype.equivFin ι).symm j)
  have hnat := canonicalPushforwardCohomologyMap_naturality f
    ((e Y).hom ≫ Pi.π (fun _ : ι => residueModule φ Y) ((Fintype.equivFin ι).symm j)) n
  have key : (relativeCohomology X.hom n).map k ≫
      canonicalPushforwardCohomologyMap f (ideal φ Y) n ≫
      (relativeCohomology Y.hom n).map
        ((e Y).hom ≫ Pi.π (fun _ : ι => residueModule φ Y) ((Fintype.equivFin ι).symm j)) ≫
      canonicalPushforwardCohomologyMap (residueιOver φ Y)
        (SheafOfModules.unit ((residuePullback φ).obj Y).left.ringCatSheaf) n ≫
      (residueBaseRingIso φ n Y).hom.app _ =
    (relativeCohomology X.hom n).map
        ((e X).hom ≫ Pi.π (fun _ : ι => residueModule φ X) ((Fintype.equivFin ι).symm j)) ≫
      canonicalPushforwardCohomologyMap (residueιOver φ X)
        (SheafOfModules.unit ((residuePullback φ).obj X).left.ringCatSheaf) n ≫
      (residueBaseRingIso φ n X).hom.app _ ≫
      (ModuleCat.restrictScalars (residueRingHom φ).hom).map
        (relativeCohomologyPullback ((residuePullback φ).map f)
            (SheafOfModules.unit ((residuePullback φ).obj X).left.ringCatSheaf) n ≫
          (relativeCohomology ((residuePullback φ).obj Y).hom n).map
            (pullbackUnitIso ((residuePullback φ).map f).left).hom) := by
    rw [← reassoc_of% hnat, ← Functor.map_comp_assoc, hsq]
    simp only [Functor.map_comp, Category.assoc]
    rw [coordinate_square, Functor.map_comp]
  have hx := congrArg (fun q => ModuleCat.Hom.hom q x) key
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hx
  rw [coordinateEquiv_apply, coordinateEquiv_apply, structurePull]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  refine hx.trans ?_
  rfl

end Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology
