import Langlands.AlgebraicGeometry.Modules.PushforwardComparison

/-!
# Base change maps on cohomology over affine bases

For a commutative square of schemes `g ≫ f = f' ≫ Spec.map φ` with `f : X ⟶ Spec R`,
`f' : X' ⟶ Spec R'` and `φ : R ⟶ R'`, and an `𝒪_X`-module `M` whose pullback `g^* M` has
vanishing higher direct images along `g`, this file constructs the `φ`-semilinear base change map
`Hⁿ_R(X, M) ⟶ Hⁿ_{R'}(X', g^* M)` and proves that it is natural in `M`.
-/

noncomputable section

universe u v u' v' u'' v''

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicGeometry

namespace Langlands.Cohomology.AcyclicResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {E : Type u''} [Category.{v''} E] [Abelian E]

/-- `mapAugmentation` is compatible with cochain maps of injective resolutions over a map. -/
lemma mapAugmentation_naturality (F : C ⥤ D) [F.Additive] {A B : C} (u : A ⟶ B)
    (I : InjectiveResolution A) (J : InjectiveResolution B) (ψ : I.cocomplex ⟶ J.cocomplex)
    (hψ : I.ι ≫ ψ = (CochainComplex.single₀ C).map u ≫ J.ι) :
    mapAugmentation F I ≫ (F.mapHomologicalComplex _).map ψ =
      (CochainComplex.single₀ D).map (F.map u) ≫ mapAugmentation F J := by
  ext
  have h0 := HomologicalComplex.congr_hom hψ 0
  simp only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero] at h0
  simp only [HomologicalComplex.comp_f, mapAugmentation_f_zero,
    Functor.mapHomologicalComplex_map_f, CochainComplex.single₀_map_f_zero,
    CochainComplex.single₀ObjXSelf, Iso.refl_inv]
  exact (F.map_comp _ _).symm.trans ((congrArg F.map
    ((congrArg (· ≫ ψ.f 0) (Category.id_comp (I.ι.f 0))).trans
      (h0.trans (congrArg (u ≫ ·) (Category.id_comp (J.ι.f 0)).symm)))).trans
    (F.map_comp _ _))

section Composite

variable [HasInjectiveResolutions C] [HasInjectiveResolutions D]
  {F : C ⥤ D} [F.Additive] [PreservesFiniteLimits F] (G : D ⥤ E) [G.Additive]
  {H : C ⥤ E} [H.Additive] (e : F ⋙ G ≅ H)

/-- `compComparison` is natural in the object. -/
@[reassoc]
theorem compComparison_naturality {A B : C} (u : A ⟶ B)
    (hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A))
    (hB : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj B)) (n : ℕ) :
    (H.rightDerived n).map u ≫ compComparison G e B hB n =
      compComparison G e A hA n ≫ (G.rightDerived n).map (F.map u) := by
  have := quasiIso_mapAugmentation F (injectiveResolution A) hA
  have := quasiIso_mapAugmentation F (injectiveResolution B) hB
  let ψ := InjectiveResolution.desc u (injectiveResolution B) (injectiveResolution A)
  have h1 := InjectiveResolution.isoRightDerivedObj_hom_naturality u (injectiveResolution A)
    (injectiveResolution B) ψ (InjectiveResolution.desc_commutes_zero _ _ _) H n
  have h2 := resolutionComparison_naturality G (mapAugmentation F (injectiveResolution A))
    (mapAugmentation F (injectiveResolution B)) (F.map u) ((F.mapHomologicalComplex _).map ψ)
    (mapAugmentation_naturality F u _ _ ψ (InjectiveResolution.desc_commutes _ _ _)) n
  have h3 : (H.mapHomologicalComplex _).map ψ ≫
      (Functor.mapHomologicalComplexCompIso e _).inv.app (injectiveResolution B).cocomplex =
      (Functor.mapHomologicalComplexCompIso e _).inv.app (injectiveResolution A).cocomplex ≫
        (G.mapHomologicalComplex _).map ((F.mapHomologicalComplex _).map ψ) :=
    (Functor.mapHomologicalComplexCompIso e _).inv.naturality ψ
  simp only [compComparison, Category.assoc]
  rw [reassoc_of% h1, ← h2]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc, h3, Functor.map_comp_assoc]

end Composite

end Langlands.Cohomology.AcyclicResolution

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

open Langlands.Cohomology.AcyclicResolution

section Naturality

variable {X Y : Scheme.{u}} (h : X ⟶ Y) {R : CommRingCat.{u}} (g : Y ⟶ Spec R)

/-- `pushforwardComparison` is natural in the module. -/
@[reassoc]
theorem pushforwardComparison_naturality {M N : X.Modules} (u : M ⟶ N)
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage h (q + 1)).obj M))
    (hN : ∀ q : ℕ, IsZero ((higherDirectImage h (q + 1)).obj N)) (n : ℕ) :
    (relativeCohomology (h ≫ g) n).map u ≫ pushforwardComparison h g N hN n =
      pushforwardComparison h g M hM n ≫
        (relativeCohomology g n).map ((Scheme.Modules.pushforward h).map u) :=
  compComparison_naturality _ _ u hM hN n

end Naturality

section BaseRing

variable {X : Scheme.{u}} {R R' : CommRingCat.{u}} (φ : R ⟶ R') (f : X ⟶ Spec R)
  (f' : X ⟶ Spec R')

/-- If `f = f' ≫ Spec.map φ`, then `structureRingHom f = φ ≫ structureRingHom f'`. -/
lemma structureRingHom_eq_comp (w : f = f' ≫ Spec.map φ) :
    structureRingHom f = φ ≫ structureRingHom f' := by
  subst w
  simp [structureRingHom]

/-- If `f = f' ≫ Spec.map φ`, then the `R`-module cohomology along `f` is the `R'`-module
cohomology along `f'` with scalars restricted along `φ`. -/
def relativeCohomologyBaseRingIso (w : f = f' ≫ Spec.map φ) (n : ℕ) :
    relativeCohomology f n ≅ relativeCohomology f' n ⋙ ModuleCat.restrictScalars φ.hom :=
  (relativeCohomologyRestrictScalarsIso f n).symm ≪≫
    Functor.isoWhiskerLeft (cohomology X n)
      (ModuleCat.restrictScalarsComp' φ.hom (structureRingHom f').hom (structureRingHom f).hom
        (by rw [structureRingHom_eq_comp φ f f' w, CommRingCat.hom_comp])) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (relativeCohomologyRestrictScalarsIso f' n) _

end BaseRing

section BaseChange

variable {X X' : Scheme.{u}} {R R' : CommRingCat.{u}} (φ : R ⟶ R') (f : X ⟶ Spec R)
  (f' : X' ⟶ Spec R') (g : X' ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)

/-- The `φ`-semilinear base change map `Hⁿ_R(X, M) ⟶ Hⁿ_{R'}(X', g^* M)` for the square
`g ≫ f = f' ≫ Spec.map φ`: the map induced by the unit `M ⟶ g_* g^* M`, followed by the inverse
of `pushforwardComparison g f (g^* M)` and the identification of `R`-module cohomology along
`g ≫ f` with `R'`-module cohomology along `f'`. -/
def baseChangeMap (M : X.Modules)
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pullback g).obj M)))
    (hJ : ∀ J : X'.Modules, Injective J → ∀ q : ℕ,
      IsZero ((relativeCohomology f (q + 1)).obj ((Scheme.Modules.pushforward g).obj J)))
    (n : ℕ) :
    (relativeCohomology f n).obj M ⟶
      (ModuleCat.restrictScalars φ.hom).obj
        ((relativeCohomology f' n).obj ((Scheme.Modules.pullback g).obj M)) :=
  haveI := isIso_pushforwardComparison g f _ hM hJ n
  (relativeCohomology f n).map ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) ≫
    inv (pushforwardComparison g f _ hM n) ≫
    (relativeCohomologyBaseRingIso φ (g ≫ f) f' w n).hom.app _

/-- The base change map is natural in the module. -/
theorem baseChangeMap_naturality {M N : X.Modules} (u : M ⟶ N)
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pullback g).obj M)))
    (hN : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pullback g).obj N)))
    (hJ : ∀ J : X'.Modules, Injective J → ∀ q : ℕ,
      IsZero ((relativeCohomology f (q + 1)).obj ((Scheme.Modules.pushforward g).obj J)))
    (n : ℕ) :
    (relativeCohomology f n).map u ≫ baseChangeMap φ f f' g w N hN hJ n =
      baseChangeMap φ f f' g w M hM hJ n ≫
        (ModuleCat.restrictScalars φ.hom).map
          ((relativeCohomology f' n).map ((Scheme.Modules.pullback g).map u)) := by
  have := isIso_pushforwardComparison g f _ hM hJ n
  have := isIso_pushforwardComparison g f _ hN hJ n
  have hu := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality u
  have hc := pushforwardComparison_naturality g f ((Scheme.Modules.pullback g).map u) hM hN n
  have hc' : (relativeCohomology f n).map
        ((Scheme.Modules.pushforward g).map ((Scheme.Modules.pullback g).map u)) ≫
        inv (pushforwardComparison g f _ hN n) =
      inv (pushforwardComparison g f _ hM n) ≫
        (relativeCohomology (g ≫ f) n).map ((Scheme.Modules.pullback g).map u) := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    exact hc.symm
  have hi := (relativeCohomologyBaseRingIso φ (g ≫ f) f' w n).hom.naturality
    ((Scheme.Modules.pullback g).map u)
  simp only [Functor.id_map, Functor.comp_map] at hu
  simp only [baseChangeMap, Category.assoc]
  rw [← Functor.map_comp_assoc, hu, Functor.map_comp_assoc]
  simp only [Functor.comp_map] at hi ⊢
  rw [reassoc_of% hc', hi]

end BaseChange

end Langlands.AlgebraicGeometry.Modules.DerivedSections
