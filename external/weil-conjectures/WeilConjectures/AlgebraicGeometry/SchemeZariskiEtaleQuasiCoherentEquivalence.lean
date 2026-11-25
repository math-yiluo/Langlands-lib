/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleTensorOpenSectionsNaturality
public import WeilConjectures.AlgebraicGeometry.GabberH0ZariskiConstructions
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.CoherentFiniteType
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import WeilConjectures.AlgebraicGeometry.Morphisms.FpqcDescent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import WeilConjectures.AlgebraicGeometry.Sites.Ga
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

/-!
# Quasi-coherent modules on the Zariski and small étale sites

Source: Stacks Project, Descent, Tags 03FH, 03DX, 03LC, 05VG and 0GN7
(blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- The ring-valued presheaf of regular functions on the small étale site.
Source: Stacks 03DU (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def smallEtaleModulePresheaf (X : Scheme.{u}) : X.Etaleᵒᵖ ⥤ RingCat.{u} :=
  X.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}

/-- Regular functions form a ring sheaf on the small étale site.
Source: Stacks 03DU (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence).
Proof: the underlying set presheaf is the regular-function sheaf by étale descent
(upstream isSheaf_etaleStructurePresheaf). Compatible ring homomorphisms glue pointwise;
the sheaf separatedness identities show that the glued map preserves every ring operation.
This proves the ring-valued sheaf condition without any enlargement of section rings. -/
theorem smallEtaleModulePresheaf_isSheaf (X : Scheme.{u}) :
    Presheaf.IsSheaf X.smallEtaleTopology (smallEtaleModulePresheaf X) := by
  have h : Presieve.IsSheaf X.smallEtaleTopology
      (smallEtaleModulePresheaf X ⋙ CategoryTheory.forget RingCat) :=
    X.isSheaf_etaleStructurePresheaf_comp_forget
  intro E V S hS x hx
  have hQ := h S hS
  let y (e : E) : Presieve.FamilyOfElements
      (smallEtaleModulePresheaf X ⋙ CategoryTheory.forget RingCat) S :=
    fun W f hf ↦ (x f hf).hom e
  have hy (e : E) : (y e).Compatible := by
    intro W₁ W₂ Z g₁ g₂ f₁ f₂ h₁ h₂ fac
    exact congrArg (fun φ : E ⟶ (smallEtaleModulePresheaf X).obj (op Z) ↦ φ.hom e)
      (hx g₁ g₂ h₁ h₂ fac)
  let g (e : E) : (smallEtaleModulePresheaf X).obj (op V) :=
    hQ.amalgamate (y e) (hy e)
  have hg (e : E) {W : X.Etale} (f : W ⟶ V) (hf : S f) :
      (smallEtaleModulePresheaf X).map f.op (g e) = (x f hf).hom e :=
    hQ.valid_glue (hy e) f hf
  have ext {a b : (smallEtaleModulePresheaf X).obj (op V)}
      (hab : ∀ {W : X.Etale} (f : W ⟶ V),
        S f → (smallEtaleModulePresheaf X).map f.op a =
          (smallEtaleModulePresheaf X).map f.op b) : a = b :=
    hQ.isSeparatedFor.ext fun _ f hf ↦ hab f hf
  let φ : E ⟶ (smallEtaleModulePresheaf X).obj (op V) := RingCat.ofHom
    { toFun := g
      map_one' := ext fun f hf ↦ by rw [hg _ f hf, map_one, map_one]
      map_mul' := fun a b ↦ ext fun f hf ↦ by
        rw [map_mul, hg _ f hf, hg _ f hf, hg _ f hf, map_mul]
      map_zero' := ext fun f hf ↦ by rw [hg _ f hf, map_zero, map_zero]
      map_add' := fun a b ↦ ext fun f hf ↦ by
        rw [map_add, hg _ f hf, hg _ f hf, hg _ f hf, map_add] }
  refine ⟨φ, fun W f hf ↦ ?_, fun ψ hψ ↦ ?_⟩
  · change φ ≫ (smallEtaleModulePresheaf X).map f.op = x f hf
    ext e
    exact hg e f hf
  · refine RingCat.hom_ext (RingHom.ext fun e ↦ ?_)
    refine ext fun f hf ↦ ?_
    exact (congrArg (fun χ : E ⟶ (smallEtaleModulePresheaf X).obj (op _) ↦ χ.hom e)
      (hψ f hf)).trans (hg e f hf).symm

/-- The usual structure sheaf on the small étale site, with its actual section rings.
Source: Stacks 03DU (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def smallEtaleModuleRing (X : Scheme.{u}) : Sheaf X.smallEtaleTopology RingCat.{u} :=
  ⟨smallEtaleModulePresheaf X, smallEtaleModulePresheaf_isSheaf X⟩

/-- Modules over the usual small étale structure sheaf.
Source: Stacks 03DX (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
abbrev SmallEtaleModules (X : Scheme.{u}) := SheafOfModules.{u} (smallEtaleModuleRing X)

/-- The structural map identifies functions on an open with functions on its open subscheme.
Source: Stacks 03FH (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def zariskiEtaleOpenRingMap (X : Scheme.{u})
    [hc : (AlgebraicGeometry.gabberOpenEtale X).IsContinuous
      (Opens.grothendieckTopology X) X.smallEtaleTopology] :
    X.ringCatSheaf ⟶ ((AlgebraicGeometry.gabberOpenEtale X).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology X) X.smallEtaleTopology).obj (smallEtaleModuleRing X) :=
  ⟨Functor.whiskerRight X.restrictFunctorΓ.inv (forget₂ CommRingCat.{u} RingCat.{u})⟩

/-- Restriction to Zariski opens, including restriction of scalars by the canonical ring map.
Source: Stacks 0GN7 (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def zariskiEtaleModuleRestriction (X : Scheme.{u})
    [hc : (AlgebraicGeometry.gabberOpenEtale X).IsContinuous
      (Opens.grothendieckTopology X) X.smallEtaleTopology] : SmallEtaleModules X ⥤ X.Modules :=
  SheafOfModules.pushforward (zariskiEtaleOpenRingMap X)

/-- The ring map for an arbitrary scheme morphism is pullback of regular functions.
Source: Stacks 03LC (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def smallEtaleModuleRingMap {U T : Scheme.{u}} (a : U ⟶ T) :
    smallEtaleModuleRing T ⟶ (a.Etale.sheafPushforwardContinuous RingCat.{u}
      T.smallEtaleTopology U.smallEtaleTopology).obj (smallEtaleModuleRing U) :=
  ⟨Functor.whiskerRight (etaleStructurePresheafToPullback a) (forget₂ CommRingCat.{u} RingCat.{u})⟩

/-- Direct image of small étale modules uses the scheme base-change functor on the sites.
Source: Stacks 03LC (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def smallEtaleModulePushforward {U T : Scheme.{u}} (a : U ⟶ T) :
    SmallEtaleModules U ⥤ SmallEtaleModules T :=
  SheafOfModules.pushforward (smallEtaleModuleRingMap a)

/-- The canonical ringed-site tensor pullback, left adjoint to restriction.
It represents O_et tensor over epsilon^{-1} O_Zar with epsilon^{-1} M;
Mathlib constructs this functor by module-presheaf pullback and sheafification.
Only the proof that the right adjoint exists is an argument.
Source: Stacks 03FH (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def zariskiEtaleModuleExtension (X : Scheme.{u})
    (hc : (AlgebraicGeometry.gabberOpenEtale X).IsContinuous
      (Opens.grothendieckTopology X) X.smallEtaleTopology)
    (hp : (@zariskiEtaleModuleRestriction X hc).IsRightAdjoint) :
    X.Modules ⥤ SmallEtaleModules X :=
  letI := hc
  letI : (SheafOfModules.pushforward (zariskiEtaleOpenRingMap X)).IsRightAdjoint := hp
  SheafOfModules.pullback (zariskiEtaleOpenRingMap X)

/-- The canonical tensor-extension/restriction adjunction, with its specified unit and counit.
Source: Stacks 03FH (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def zariskiEtaleModuleAdjunction (X : Scheme.{u})
    (hc : (AlgebraicGeometry.gabberOpenEtale X).IsContinuous
      (Opens.grothendieckTopology X) X.smallEtaleTopology)
    (hp : (@zariskiEtaleModuleRestriction X hc).IsRightAdjoint) :
    zariskiEtaleModuleExtension X hc hp ⊣ @zariskiEtaleModuleRestriction X hc :=
  letI := hc
  letI : (SheafOfModules.pushforward (zariskiEtaleOpenRingMap X)).IsRightAdjoint := hp
  SheafOfModules.pullbackPushforwardAdjunction (zariskiEtaleOpenRingMap X)

/-- Tensor pullback along an arbitrary morphism of small étale ringed topoi.
Source: Stacks 03LC (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def smallEtaleModulePullback {U T : Scheme.{u}} (a : U ⟶ T)
    (hp : (smallEtaleModulePushforward a).IsRightAdjoint) :
    SmallEtaleModules T ⥤ SmallEtaleModules U :=
  letI : (SheafOfModules.pushforward (smallEtaleModuleRingMap a)).IsRightAdjoint := hp
  SheafOfModules.pullback (smallEtaleModuleRingMap a)

/-- The tensor-pullback/direct-image adjunction on the small étale ringed topoi.
Source: Stacks 03LC (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def smallEtaleModuleAdjunction {U T : Scheme.{u}} (a : U ⟶ T)
    (hp : (smallEtaleModulePushforward a).IsRightAdjoint) :
    smallEtaleModulePullback a hp ⊣ smallEtaleModulePushforward a :=
  letI : (SheafOfModules.pushforward (smallEtaleModuleRingMap a)).IsRightAdjoint := hp
  SheafOfModules.pullbackPushforwardAdjunction (smallEtaleModuleRingMap a)

/-- Proof data permitting the canonical module pullback on these presented sites.
There is no chosen ring, module, map or functor in this structure.
Source: Stacks 03FH (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
structure ZariskiEtaleModuleContext (X : Scheme.{u}) where
  /-- The inclusion of open subschemes is continuous. -/
  continuous : (AlgebraicGeometry.gabberOpenEtale X).IsContinuous
    (Opens.grothendieckTopology X) X.smallEtaleTopology
  /-- Restriction of modules admits its canonical tensor left adjoint. -/
  rightAdjoint : (@zariskiEtaleModuleRestriction X continuous).IsRightAdjoint

/-- Canonical restriction, with the continuity proof supplied by the context.
Source: Stacks 0GN7 (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def ZariskiEtaleModuleContext.restriction {X : Scheme.{u}} (c : ZariskiEtaleModuleContext X) :=
  @zariskiEtaleModuleRestriction X c.continuous

/-- Canonical tensor extension for the presented sites.
Source: Stacks 03FH (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def ZariskiEtaleModuleContext.extension {X : Scheme.{u}} (c : ZariskiEtaleModuleContext X) :=
  zariskiEtaleModuleExtension X c.continuous c.rightAdjoint

/-- The canonical extension/restriction adjunction.
Source: Stacks 03FH (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def ZariskiEtaleModuleContext.adjunction {X : Scheme.{u}} (c : ZariskiEtaleModuleContext X) :
    c.extension ⊣ c.restriction :=
  zariskiEtaleModuleAdjunction X c.continuous c.rightAdjoint

/-- The canonical pullback comparison is the left-adjoint mate of the open-restriction
comparison for direct images. Its direction is (a^* F)_et to a_et^*(F_et).
Source: Stacks 03FH (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def zariskiEtalePullbackComparison {U T : Scheme.{u}} (a : U ⟶ T)
    (cU : ZariskiEtaleModuleContext U) (cT : ZariskiEtaleModuleContext T)
    (hp : (smallEtaleModulePushforward a).IsRightAdjoint)
    (r : smallEtaleModulePushforward a ⋙ cT.restriction ≅ cU.restriction ⋙ pushforward a) :
    tensorPullback a ⋙ cU.extension ≅ cT.extension ⋙ smallEtaleModulePullback a hp :=
  ((conjugateIsoEquiv
    ((Classical.choose (exists_tensorPullbackAdjunction a)).comp cU.adjunction)
    (cT.adjunction.comp (smallEtaleModuleAdjunction a hp))).symm r.symm).symm

/-- The canonical direct-image comparison, defined as the counit mate of the canonical
pullback comparison. No quasi-coherence or quasi-compactness is needed to define this map.
Source: Stacks 03LC (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def zariskiEtalePushforwardComparison {U T : Scheme.{u}} (a : U ⟶ T)
    (cU : ZariskiEtaleModuleContext U) (cT : ZariskiEtaleModuleContext T)
    (hp : (smallEtaleModulePushforward a).IsRightAdjoint)
    (r : smallEtaleModulePushforward a ⋙ cT.restriction ≅ cU.restriction ⋙ pushforward a)
    (H : U.Modules) :
    cT.extension.obj ((pushforward a).obj H) ⟶
      (smallEtaleModulePushforward a).obj (cU.extension.obj H) :=
  (smallEtaleModuleAdjunction a hp).unit.app (cT.extension.obj ((pushforward a).obj H)) ≫
    (smallEtaleModulePushforward a).map
      ((zariskiEtalePullbackComparison a cU cT hp r).inv.app ((pushforward a).obj H) ≫
        cU.extension.map ((Classical.choose (exists_tensorPullbackAdjunction a)).counit.app H))

/-- Additive sheafification on the slices of the original small étale site, retaining
u-small section groups despite the u+1 object universe of the presented site.
Source: Stacks, Sites, sheafification and the affine étale basis; Descent 03DX
(blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence).
Proof: refine each étale object by its affine opens. Affine étale schemes of finite
presentation over each affine base have a u-small skeleton: they are specified by
finite polynomial presentations over a u-small ring. Their finite jointly surjective
coverings form a basis. Apply the ordinary plus construction twice on this small basis,
then extend by compatible sections on affine covers. All products are indexed by
u-small sets; the result therefore still has u-small additive section groups. Its
usual gluing universal property is precisely the sheafification adjunction on the
slice site. The construction is invariant under changing the affine cover. -/
@[instance] theorem smallEtaleModuleOverHasWeakSheafify (T : Scheme.{u}) (V : T.Etale) :
    HasWeakSheafify (T.smallEtaleTopology.over V) AddCommGrpCat.{u} := by
  have : HasSheafify (T.smallEtaleTopology.over V) AddCommGrpCat.{u} :=
    (Scheme.Etale.overEquiv V).hasSheafify (T.smallEtaleTopology.over V)
      V.left.smallEtaleTopology AddCommGrpCat.{u}
  infer_instance

/-- Sheafification inverts exactly the locally bijective additive maps on these slices.
Source: Stacks, Sites, sheafification; Descent 03DX
(blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence).
Proof: on the affine étale basis used by smallEtaleModuleOverHasWeakSheafify, the two
plus constructions identify sections exactly when they agree locally and every section
is locally represented. Hence a locally bijective map sheafifies to an isomorphism.
Conversely the sheafification units are locally bijective, so a sheafified isomorphism
forces local injectivity and surjectivity of the original map by the same local
representatives. Refinement transfers this equivalence to the full slice site. -/
@[instance] theorem smallEtaleModuleOverWEqualsLocallyBijective
    (T : Scheme.{u}) (V : T.Etale) :
    (T.smallEtaleTopology.over V).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  have : ((Scheme.Etale.overEquiv V).inverse.sheafPushforwardContinuous
      AddCommGrpCat.{u} V.left.smallEtaleTopology
        (T.smallEtaleTopology.over V)).IsEquivalence :=
    inferInstanceAs (((Scheme.Etale.overEquiv V).sheafCongr
      (T.smallEtaleTopology.over V) V.left.smallEtaleTopology
        AddCommGrpCat.{u}).functor.IsEquivalence)
  exact GrothendieckTopology.WEqualsLocallyBijective.transport (T.smallEtaleTopology.over V)
    V.left.smallEtaleTopology (Scheme.Etale.overEquiv V).inverse
    (Functor.IsDenseSubsite.coverPreserving _ _ _)

end
end AlgebraicGeometry.Scheme.Modules
