/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence

import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring

/-!
# Inverse image on the small pro-etale site

Source: Stacks Project, Tags 09A5, 00X6, 00VC, 00VE, 00WX, 00YV, 0H7J, 03D1 and 03D2
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Base change on the small pro-etale sites. The chosen product is written with the
variable factor first, canonically the same fibre product as `X ×[Y] V`.
Source: Stacks, Tag 09A5 (auxiliary; not a blueprint node). -/
noncomputable abbrev proEtaleBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Y.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.pullback @WeaklyEtale ⊤ f

/-- Continuity of the canonical base-change functor.
Source: Stacks, Tag 09A5 (auxiliary; not a blueprint node). -/
instance proEtaleBaseChange_isContinuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (proEtaleBaseChange f).IsContinuous (ProEt.topology Y) (ProEt.topology X) :=
  ProEt.isContinuous_overPullback f

/-- Base change preserves finite limits, hence both the final object and fibre products.
Source: Stacks, Tags 09A5 and 00X6 (auxiliary; not a blueprint node). -/
instance proEtaleBaseChange_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (proEtaleBaseChange f) :=
  inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f))

/-- Base change preserves pro-etale covering sieves, by weakly etale and fpqc base change.
Source: Stacks, Tag 09A5 (auxiliary; not a blueprint node). -/
noncomputable abbrev proEtaleBaseChangeCoverPreserving {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CoverPreserving (ProEt.topology Y) (ProEt.topology X) (proEtaleBaseChange f) :=
  ProEt.coverPreserving_overPullback f

/-- Direct image, by precomposition on sections and morphisms, for any value category.
Source: Stacks, Tags 09A5, 00VC and 00WX (auxiliary; not a blueprint node). -/
noncomputable abbrev proEtaleSheafDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type v) [Category.{u + 1} D] :
    Sheaf (ProEt.topology X) D ⥤ Sheaf (ProEt.topology Y) D :=
  AlgebraicGeometry.ProEtale.lowerStar D f

/-- Inverse image is left Kan extension followed by sheafification. Its pointwise
index category is `CostructuredArrow (proEtaleBaseChange f).op (op U)`, the opposite
of the category of pairs `(V, U ⟶ u_f(V))` specified in the source.
Source: Stacks, Tags 09A5, 00VC and 00WX (auxiliary; not a blueprint node). -/
noncomputable abbrev proEtaleSheafInverseImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (ProEt.topology X) D] :
    Sheaf (ProEt.topology Y) D ⥤ Sheaf (ProEt.topology X) D :=
  Functor.sheafPullbackConstruction.sheafPullback (proEtaleBaseChange f) D
    (ProEt.topology Y) (ProEt.topology X)

/-- The constructed inverse-image/direct-image adjunction; its unit and counit are
`η_f` and `ε_f`. Take `D = Type (u+1)`, `AddCommGrpCat`, `RingCat`, or `CommRingCat`.
Source: Stacks, Tags 09A5, 00VC and 00WX (auxiliary; not a blueprint node). -/
noncomputable abbrev proEtaleSheafAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (ProEt.topology X) D] :
    proEtaleSheafInverseImage f D ⊣ proEtaleSheafDirectImage f D :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (proEtaleBaseChange f) D
    (ProEt.topology Y) (ProEt.topology X)

/-- The constant-sheaf comparison is the unique extension of the constant-section map.
Source: Stacks, Tag 0H7J (auxiliary; not a blueprint node). -/
noncomputable def proEtaleConstantDirectImageMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type v) [Category.{u + 1} D]
    [HasWeakSheafify (ProEt.topology Y) D] [HasWeakSheafify (ProEt.topology X) D]
    (A : D) :
    (constantSheaf (ProEt.topology Y) D).obj A ⟶
      (proEtaleSheafDirectImage f D).obj ((constantSheaf (ProEt.topology X) D).obj A) :=
  ((sheafificationAdjunction (ProEt.topology Y) D).homEquiv _ _).symm
    (Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))

/-- The coefficient structure map is the adjoint of the constant-section map.
Source: Stacks, Tag 0H7J (auxiliary; not a blueprint node). -/
noncomputable def proEtaleConstantInverseImageMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (ProEt.topology Y) D] [HasWeakSheafify (ProEt.topology X) D]
    (A : D) :
    (proEtaleSheafInverseImage f D).obj ((constantSheaf (ProEt.topology Y) D).obj A) ⟶
      (constantSheaf (ProEt.topology X) D).obj A :=
  (proEtaleSheafInverseImage f D).map (proEtaleConstantDirectImageMap f D A) ≫
    (proEtaleSheafAdjunction f D).counit.app _

/-- A universe-compatible small model of the pro-etale site, retaining every object.
Only the Hom universe is enlarged; no bound on schemes is changed.
Source: Stacks, Tags 09A5, 00VC and 00WX (auxiliary; not a blueprint node). -/
abbrev proEtaleSiteModel (X : Scheme.{u}) := AsSmall.{u + 1} X.ProEt

/-- The transported pro-etale topology on the small model.
Source: Stacks, Tag 09A5 (auxiliary; not a blueprint node). -/
noncomputable abbrev proEtaleModelTopology (X : Scheme.{u}) :
    GrothendieckTopology (proEtaleSiteModel X) :=
  (AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).inducedTopology (ProEt.topology X)

/-- Transport to the small model is continuous, since it is an equivalence of sites.
Source: Stacks, Tag 09A5 (auxiliary; not a blueprint node). -/
instance proEtaleModelUp_isContinuous (X : Scheme.{u}) :
    (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).IsContinuous
      (ProEt.topology X) (proEtaleModelTopology X) :=
  inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsContinuous
    (ProEt.topology X)
      ((AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.inducedTopology
        (ProEt.topology X)))

/-- Base change on the small models, obtained by transporting the original base change.
Source: Stacks, Tag 09A5 (auxiliary; not a blueprint node). -/
noncomputable abbrev proEtaleModelBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleSiteModel Y ⥤ proEtaleSiteModel X :=
  AsSmall.down ⋙ proEtaleBaseChange f ⋙ AsSmall.up

/-- Continuity of the transported base change.
Source: Stacks, Tag 09A5 (auxiliary; not a blueprint node). -/
instance proEtaleModelBaseChange_isContinuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (proEtaleModelBaseChange f).IsContinuous
      (proEtaleModelTopology Y) (proEtaleModelTopology X) :=
  haveI := Functor.isContinuous_comp (proEtaleBaseChange f) AsSmall.up
    (ProEt.topology Y) (ProEt.topology X) (proEtaleModelTopology X)
  Functor.isContinuous_comp AsSmall.down (proEtaleBaseChange f ⋙ AsSmall.up)
    (proEtaleModelTopology Y) (ProEt.topology Y) (proEtaleModelTopology X)

/-- Transport a module sheaf to the small model by sectionwise precomposition.
Source: Stacks, Tag 03D1 (auxiliary; not a blueprint node). -/
noncomputable abbrev proEtaleModuleToModel {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1}) :=
  SheafOfModules.pushforward.{u + 1} (F := AsSmall.down)
    (J := proEtaleModelTopology X) (K := ProEt.topology X)
    (R := R) (𝟙 _)

/-- Transport back from the small model. The two transports are mutually inverse on
sections and linear maps; no choice of module data occurs.
Source: Stacks, Tag 03D1 (auxiliary; not a blueprint node). -/
noncomputable abbrev proEtaleModuleFromModel {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1}) :=
  SheafOfModules.pushforward.{u + 1} (F := AsSmall.up)
    (J := ProEt.topology X) (K := proEtaleModelTopology X)
    (S := R) (R := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
      RingCat.{u + 1}
        (proEtaleModelTopology X) (ProEt.topology X)).obj R) (𝟙 R)

/-- The unit ring map on the transported sites, obtained from the actual ring inverse
image adjunction and then forgetting commutativity.
Source: Stacks, Tags 00YV and 03D2 (auxiliary; not a blueprint node). -/
noncomputable def proEtaleModelRingUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
      RingCat.{u + 1} (proEtaleModelTopology Y) (ProEt.topology Y)).obj
        ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⟶
    ((proEtaleModelBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
      (proEtaleModelTopology Y) (proEtaleModelTopology X)).obj
        (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
          RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj
            ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))) :=
  ⟨Functor.whiskerLeft AsSmall.down.op
    (((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R)).hom)⟩

/-- Inverse image of module sheaves over the inverse-image ring. The small-model
pullback is the sheafified module Kan extension along the adjunction unit. Thus the
ring and module actions are the images of the original actions. Transport back
retains the original small pro-etale sites with object universe `u+1`, Hom universe `u`.
Source: Stacks, Tags 00YV and 03D2 (auxiliary; not a blueprint node). -/
noncomputable def proEtaleModuleInverseImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⥤
    SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)) :=
  proEtaleModuleToModel
      ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⋙
    SheafOfModules.pullback (proEtaleModelRingUnit f R) ⋙
    proEtaleModuleFromModel
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))

/-- The category of pairs `(V, φ : U ⟶ u_f(V))`; morphisms are exactly arrows
`a : V ⟶ V′` satisfying `φ ≫ u_f(a) = φ′`. The inverse-image colimit uses its opposite.
Source: Stacks, Tag 00VC (auxiliary; not a blueprint node). -/
noncomputable abbrev proEtaleInverseImageIndex {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.ProEt) :=
  StructuredArrow U (proEtaleBaseChange f)

/-- The constant commutative ring sheaf `A_X`, as a sheaf of commutative rings (before
forgetting commutativity).
Source: Stacks, Tag 0H7J (auxiliary; not a blueprint node). -/
noncomputable abbrev proEtaleConstantRing (X : Scheme.{u}) (A : Type u) [CommRing A] :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1, u} A))

/-- The canonical `ρ_A^f`, with its sectionwise constant-section normalization.
Source: Stacks, Tag 0H7J (auxiliary; not a blueprint node). -/
noncomputable abbrev proEtaleCoefficientDirectImageMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] :
    proEtaleConstantRing Y A ⟶
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (proEtaleConstantRing X A) :=
  proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
    (CommRingCat.of (ULift.{u + 1, u} A))

/-- The canonical `c_A^f = f⁻¹(ρ_A^f) ≫ ε_f`, retaining commutativity for tensor products.
Source: Stacks, Tag 0H7J (auxiliary; not a blueprint node). -/
noncomputable abbrev proEtaleCoefficientInverseImageMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (proEtaleConstantRing Y A) ⟶
      proEtaleConstantRing X A :=
  proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
    (CommRingCat.of (ULift.{u + 1, u} A))

/-- Direct image of constant-coefficient modules: sectionwise precomposition and
restriction of scalars through `ρ_A^f`. Morphisms are the original sectionwise linear maps.
Source: Stacks, Tag 03D1 (auxiliary; not a blueprint node). -/
noncomputable def proEtaleConstantModuleDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X)
    (S := (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing Y A))
    (R := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A))
    ⟨Functor.whiskerRight (proEtaleCoefficientDirectImageMap f A).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- Module pullback: inverse image over `f⁻¹ A_Y`, followed by the specified sheaf
extension of scalars along `c_A^f`. This is the sheafification of the sectionwise tensor,
not a chosen arbitrary left adjoint or a replacement coefficient category.
Source: Stacks, Tag 03D2 (auxiliary; not a blueprint node). -/
noncomputable def proEtaleConstantModulePullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A]
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing Y A))) :
    SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A)) :=
  SheafOfModules.changeOfRings.{u, u + 1, u + 1} (proEtaleCoefficientInverseImageMap f A)
    ((proEtaleModuleInverseImage f (proEtaleConstantRing Y A)).obj M)

/-- The map on module pullbacks is inverse image of the linear map followed by
extension of scalars, with the induced maps on pure tensors and sheafification.
Source: Stacks, Tag 03D2 (auxiliary; not a blueprint node). -/
noncomputable def proEtaleConstantModulePullbackMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A]
    {M N : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing Y A))}
    (a : M ⟶ N) :
    proEtaleConstantModulePullback f A M ⟶ proEtaleConstantModulePullback f A N :=
  SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} (proEtaleCoefficientInverseImageMap f A) _
    ((proEtaleModuleInverseImage f (proEtaleConstantRing Y A)).map a)

end AlgebraicGeometry.Scheme
