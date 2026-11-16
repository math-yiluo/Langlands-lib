import Langlands.AlgebraicGeometry.Modules.FinitePresentationDescent
import Langlands.AlgebraicGeometry.Modules.RelativeFlatnessDescent
import Langlands.AlgebraicGeometry.Modules.AffineDirectImageRank
import Langlands.AlgebraicGeometry.Modules.RankOneStalkReflection
import Langlands.AlgebraicGeometry.Picard.FiniteLocallyFreeDeterminant
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # Descent of finite local bases -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Modules

variable {X Y : Scheme.{u}}

/-- The stalk of a finite free module sheaf is the corresponding finite power
of the actual local ring. -/
def finiteFreeStalkIso (X : Scheme.{u}) (I : Type u) [Finite I] (x : X) :
    (stalkFunctor x).obj (SheafOfModules.free (R := X.ringCatSheaf) I) ≅
      ModuleCat.of (X.presheaf.stalk x) (I → X.presheaf.stalk x) := by
  let E := stalkFunctor x
  letI := (StalkAdjunction.adjunction x).isLeftAdjoint
  letI := Fintype.ofFinite I
  let e := Fintype.equivFin I
  exact E.mapIso (Sigma.reindex e
      (fun _ : Fin (Fintype.card I) => SheafOfModules.unit X.ringCatSheaf)) ≪≫
    PreservesCoproduct.iso E
      (fun _ : Fin (Fintype.card I) => SheafOfModules.unit X.ringCatSheaf) ≪≫
    (biproduct.isoCoproduct
      (fun _ : Fin (Fintype.card I) => E.obj (SheafOfModules.unit X.ringCatSheaf))).symm ≪≫
    ModuleCat.biproductIsoPi _ ≪≫
    (LinearEquiv.piCongrRight
      (fun _ : Fin (Fintype.card I) => unitStalkLinearEquiv X x)).toModuleIso ≪≫
    (LinearEquiv.piCongrLeft (X.presheaf.stalk x)
      (fun _ : I => X.presheaf.stalk x) e.symm).toModuleIso

/-- Finite local bases give local finite presentation. -/
lemma isFinitePresentation_of_hasFiniteLocalBasis (M : X.Modules)
    (h : Langlands.Scheme.Modules.HasFiniteLocalBasis M) : M.IsFinitePresentation := by
  obtain ⟨q, hq, hf⟩ := h
  let := hq
  let := hf
  refine SheafOfModules.IsFinitePresentation.mk.{u, u, u} ⟨q.quasiCoherentData, ?_⟩
  constructor
  intro i
  exact {
    isFiniteType_generators := hf.isFiniteType i
    isFiniteType_relations := by
      constructor
      change Finite (ULift Empty)
      infer_instance }

/-- Finite local bases make every actual stalk flat over its local ring. -/
lemma flat_stalk_of_hasFiniteLocalBasis (M : X.Modules)
    (h : Langlands.Scheme.Modules.HasFiniteLocalBasis M) (x : X) :
    Module.Flat (X.presheaf.stalk x) (stalk M x) := by
  obtain ⟨q, hq, hf⟩ := h
  let := hq
  let := hf
  have hx : x ∈ ⨆ i, q.X i :=
    (_root_.Opens.coversTop_iff X q.X).mp q.coversTop ▸
      (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  let U : X.Opens := q.X i
  let y : U.toScheme := ⟨x, hxi⟩
  have : (q.generators i).IsFiniteType := hf.isFiniteType i
  have : IsIso (q.generators i).π := hq.isIso i
  let G := generatingSectionsRestrict M U (q.generators i)
  have : G.IsFiniteType := by dsimp [G]; infer_instance
  have : IsIso G.π := by
    change IsIso (((q.generators i).map (Scheme.Modules.overEquiv U).functor
      (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm).ofEpi
        ((Scheme.Modules.overFunctorEquiv U).app M).hom).π
    rw [SheafOfModules.GeneratingSections.ofEpi_π]
    rw [SheafOfModules.GeneratingSections.map_π_eq]
    exact (show IsIso ((SheafOfModules.mapFreeIso (Scheme.Modules.overEquiv U).functor
      (q.generators i).I (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm ≪≫
        (Scheme.Modules.overEquiv U).functor.mapIso (asIso (q.generators i).π) ≪≫
        (Scheme.Modules.overFunctorEquiv U).app M).hom) from inferInstance)
  let e := (stalkFunctor y).mapIso (asIso G.π).symm ≪≫
    finiteFreeStalkIso U.toScheme G.I y
  have : Module.Flat (U.toScheme.presheaf.stalk y)
      (stalk (M.restrict U.ι) y) := Module.Flat.of_linearEquiv e.toLinearEquiv
  let := (U.ι.stalkMap y).hom.toAlgebra
  let := relativeStalkModule U.ι (M.restrict U.ι) y
  have : IsScalarTower (X.presheaf.stalk (U.ι y)) (U.toScheme.presheaf.stalk y)
      (stalk (M.restrict U.ι) y) := .of_algebraMap_smul (fun _ _ => rfl)
  have : Module.Flat (X.presheaf.stalk (U.ι y)) (U.toScheme.presheaf.stalk y) :=
    Flat.stalkMap U.ι y
  have : Module.Flat (X.presheaf.stalk (U.ι y)) (stalk (M.restrict U.ι) y) :=
    Module.Flat.trans _ (U.toScheme.presheaf.stalk y) _
  change Module.Flat (X.presheaf.stalk (U.ι y)) (stalk M (U.ι y))
  exact Module.Flat.of_linearEquiv (restrictStalkLinearEquiv U.ι M y).symm

/-- Transport a finite free stalk chart to an open restriction, using its
actual local-ring isomorphism on every coordinate. -/
def restrictStalkFiniteFreeEquiv {Z : Scheme.{u}} (f : Z ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (z : Z) (I : Type u)
    (e : stalk M (f z) ≃ₗ[X.presheaf.stalk (f z)] (I → X.presheaf.stalk (f z))) :
    stalk (M.restrict f) z ≃ₗ[Z.presheaf.stalk z] (I → Z.presheaf.stalk z) := by
  let eR := (asIso (f.stalkMap z)).commRingCatIsoToRingEquiv
  let eS : stalk (M.restrict f) z ≃+ stalk M (f z) :=
    ((Scheme.Modules.restrictStalkNatIso f z).app M).addCommGroupIsoToAddEquiv
  let eP := AddEquiv.piCongrRight (fun _ : I => eR.toAddEquiv)
  refine {
    __ := (eS.trans e.toAddEquiv).trans eP
    map_smul' := ?_ }
  intro a m
  obtain ⟨r, rfl⟩ := eR.surjective a
  ext j
  have h := (restrictStalkLinearEquiv f M z).map_smul r m
  change eR (e (eS ((f.stalkMap z) r • m)) j) =
    eR r * eR (e (eS m) j)
  change eS ((f.stalkMap z) r • m) = r • eS m at h
  rw [h, e.map_smul]
  exact eR.map_mul _ _

/-- A finite basis at an actual affine stalk spreads to an actual finite free
chart, when the module of affine sections is finitely presented. -/
lemma exists_freeNeighborhood_of_spec_stalk_basis {R : CommRingCat.{u}}
    (P : (Spec R).Modules) [P.IsQuasicoherent]
    [Module.FinitePresentation Γ(Spec R, ⊤) Γ(P, ⊤)]
    (x : Spec R) (I : Type u) [Finite I]
    (b : Module.Basis I ((Spec R).presheaf.stalk x) (stalk P x)) :
    ∃ U : (Spec R).Opens, x ∈ U ∧ Nonempty
      (P.restrict U.ι ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) I) := by
  let N := moduleSpecΓFunctor.obj P
  have : Module.FinitePresentation R N := finitePresentation_moduleSpecΓFunctor P
  let t : tilde N ≅ P := asIso P.fromTildeΓ
  let : Algebra R ((Spec R).presheaf.stalk x) :=
    inferInstanceAs (Algebra R ((structurePresheafInCommRingCat R).stalk x))
  let : IsLocalization x.asIdeal.primeCompl ((Spec R).presheaf.stalk x) :=
    inferInstanceAs (IsLocalization x.asIdeal.primeCompl
      ((structurePresheafInCommRingCat R).stalk x))
  let : IsScalarTower R ((Spec R).presheaf.stalk x) (stalk (tilde N) x) :=
    inferInstanceAs (IsScalarTower R ((structurePresheafInCommRingCat R).stalk x)
      ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R N).presheaf x))
  obtain ⟨r, hr, b', _⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
    x.asIdeal.primeCompl (tilde.toStalk N x).hom ((Spec R).presheaf.stalk x)
    (b.map (stalkIso t x).symm)
  let e := LocalizedModule.equivTensorProduct (Submonoid.powers r) N
  exact ⟨PrimeSpectrum.basicOpen r, hr,
    ⟨DerivedSections.freeChartOfLocalizedBasis P r I (b'.map e)⟩⟩

/-- A finite actual stalk basis of a locally finitely presented module sheaf
spreads to an actual finite free chart on an open neighbourhood. -/
lemma exists_freeNeighborhood_of_stalk_basis (M : X.Modules) [M.IsFinitePresentation]
    (x : X) (I : Type u) [Finite I]
    (b : Module.Basis I (X.presheaf.stalk x) (stalk M x)) :
    ∃ U : X.Opens, x ∈ U ∧ Nonempty
      (M.restrict U.ι ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) I) := by
  obtain ⟨R, f, hf, y, hy, hM⟩ := exists_Spec_finitePresentation_sections M x
  let := hf
  let := hM
  subst x
  let c := Module.Basis.ofEquivFun (restrictStalkFiniteFreeEquiv f M y I b.equivFun)
  obtain ⟨U, hyU, ⟨e⟩⟩ :=
    exists_freeNeighborhood_of_spec_stalk_basis (M.restrict f) y I c
  let g := U.ι ≫ f
  let t : M.restrict g ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) I :=
    (Scheme.Modules.restrictFunctorComp U.ι f).app M ≪≫ e
  let E : M.restrict g.opensRange.ι ≅
      SheafOfModules.free (R := g.opensRange.toScheme.ringCatSheaf) I :=
    (Scheme.Modules.restrictFunctorCongr (Scheme.Hom.isoOpensRange_inv_comp g).symm).app M ≪≫
      (Scheme.Modules.restrictFunctorComp g.isoOpensRange.inv g).app M ≪≫
      (Scheme.Modules.restrictFunctor g.isoOpensRange.inv).mapIso t ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback g.isoOpensRange.inv).app _ ≪≫
      SheafOfModules.pullbackObjFreeIso g.isoOpensRange.inv.toRingCatSheafHom I
  exact ⟨g.opensRange, ⟨⟨y, hyU⟩, rfl⟩, ⟨E⟩⟩

/-- Local finite presentation and flatness of actual stalks give finite local
bases, with no requirement that the local ranks agree. -/
lemma hasFiniteLocalBasis_of_finitePresentation_flatStalks
    (M : X.Modules) [M.IsFinitePresentation]
    (hM : ∀ x : X, Module.Flat (X.presheaf.stalk x) (stalk M x)) :
    Langlands.Scheme.Modules.HasFiniteLocalBasis M := by
  classical
  have h : ∀ x : X, ∃ (n : ℕ) (U : X.Opens), x ∈ U ∧ Nonempty
      (M.restrict U.ι ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf)
        (ULift.{u} (Fin n))) := by
    intro x
    have := finitePresentation_stalk M x
    have := hM x
    have : Module.Free (X.presheaf.stalk x) (stalk M x) :=
      Module.free_of_flat_of_isLocalRing
    let b := (Module.finBasis (X.presheaf.stalk x) (stalk M x)).reindex Equiv.ulift.symm
    obtain ⟨U, hxU, e⟩ := exists_freeNeighborhood_of_stalk_basis M x
      (ULift.{u} (Fin (Module.finrank (X.presheaf.stalk x) (stalk M x)))) b
    exact ⟨_, U, hxU, e⟩
  choose n U hx e using h
  refine ⟨Langlands.Scheme.Modules.freeNeighborhoodGenerators M U hx
      (fun x => ULift.{u} (Fin (n x))) (fun x => (e x).some),
    Langlands.Scheme.Modules.freeNeighborhoodGenerators_isLocallyFreeData M U hx
      (fun x => ULift.{u} (Fin (n x))) (fun x => (e x).some), ?_⟩
  constructor
  intro x
  change ((SheafOfModules.free.generatingSections (ULift.{u} (Fin (n x)))).ofEpi _).IsFiniteType
  exact ⟨inferInstanceAs (Finite (ULift.{u} (Fin (n x))))⟩

/-- Finite local bases descend along an fppf covering morphism. -/
lemma hasFiniteLocalBasis_of_pullback_fppf (p : X ⟶ Y)
    [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (M : Y.Modules)
    (hM : Langlands.Scheme.Modules.HasFiniteLocalBasis ((Scheme.Modules.pullback p).obj M)) :
    Langlands.Scheme.Modules.HasFiniteLocalBasis M := by
  let N := (Scheme.Modules.pullback p).obj M
  have : N.IsFinitePresentation := isFinitePresentation_of_hasFiniteLocalBasis N hM
  have : M.IsFinitePresentation := isFinitePresentation_of_pullback_fppf p M
  apply hasFiniteLocalBasis_of_finitePresentation_flatStalks M
  intro y
  obtain ⟨x, rfl⟩ := p.surjective y
  let A := Y.presheaf.stalk (p x)
  let B := X.presheaf.stalk x
  let : Algebra A B := (p.stalkMap x).hom.toAlgebra
  have : Module.Flat B (stalk N x) := flat_stalk_of_hasFiniteLocalBasis N hM x
  have : Module.Flat B (B ⊗[A] stalk M (p x)) :=
    Module.Flat.of_linearEquiv (StalkPullback.pullbackStalkTensorEquiv p x M).symm
  have : Module.Flat A B := Flat.stalkMap p x
  have : Module.Flat A (B ⊗[A] stalk M (p x)) :=
    Module.Flat.trans A B _
  have : Module.FaithfullyFlat A B := faithfullyFlat_stalkMap p x
  exact RelativeFlatnessDescent.flat_of_faithfullyFlat_tensor A A B (stalk M (p x))

/-- Choose actual finite local basis data on the original module from finite
local bases of its fppf pullback. -/
def finiteLocalBasisOfPullbackFppf (p : X ⟶ Y)
    [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (M : Y.Modules)
    (hM : Langlands.Scheme.Modules.HasFiniteLocalBasis ((Scheme.Modules.pullback p).obj M)) :
    {q : SheafOfModules.LocalGeneratorsData.{u} M // q.IsLocallyFreeData ∧ q.IsFiniteType} :=
  let h := hasFiniteLocalBasis_of_pullback_fppf p M hM
  ⟨h.choose, h.choose_spec⟩

end Langlands.AlgebraicGeometry.Modules
