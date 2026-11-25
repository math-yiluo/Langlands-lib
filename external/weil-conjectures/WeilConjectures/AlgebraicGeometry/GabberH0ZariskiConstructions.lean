/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveSetDescentInjective
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleCore

/-! # Explicit Zariski restriction and section transport

Source: Stacks Project, Tag 09ZF, fourth proof paragraph; Tag 01JR.
(blueprint: def-weil-pbc-gabber-h0-zariski-constructions).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The canonical open-subscheme inclusion into the etale site.
Source: Stacks Project, Tag 09ZF, fourth proof paragraph; Sites, Tags 03CB and 03CC.
(blueprint: def-weil-pbc-gabber-h0-zariski-constructions). -/
noncomputable def gabberOpenEtale (X : Scheme.{u}) : X.Opens ⥤ X.Etale :=
  MorphismProperty.Comma.lift X.restrictFunctor
    (fun U ↦ (inferInstance : Etale U.ι)) (fun _ ↦ trivial) (fun _ ↦ trivial)

/-- The canonical inclusion is continuous. Source: Stacks, Tags 00X6 and 00X5.
(blueprint: def-weil-pbc-gabber-h0-zariski-constructions).
Proof: an open covering is jointly surjective as a family of etale maps, so its
image sieve is an etale covering. The inclusion preserves pullbacks, and the
cover-preserving criterion therefore gives continuity. -/
theorem gabberOpenEtale_continuous (X : Scheme.{u}) :
    (gabberOpenEtale X).IsContinuous
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology := by
  obtain ⟨j, hj, _, _, _, hc, _⟩ := zariski_to_etale_core X
  let : j.IsContinuous (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology := hc
  have he : j ≅ gabberOpenEtale X :=
    Functor.fullyFaithfulCancelRight (Scheme.Etale.forget X) (eqToIso hj)
  exact Functor.isContinuous_of_iso he _ _

/-- Restrict an etale sheaf by precomposition with the canonical inclusion.
Source: Stacks Project, Tag 09ZF, fourth proof paragraph; Sites, Tags 03CB and 03CC.
(blueprint: def-weil-pbc-gabber-h0-zariski-constructions). -/
noncomputable def gabberZariskiSheaf (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    TopCat.Sheaf (Type (u + 1)) X.toTopCat :=
  let : (gabberOpenEtale X).IsContinuous
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology :=
    gabberOpenEtale_continuous X
  ((gabberOpenEtale X).sheafPushforwardContinuous (Type (u + 1))
    (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F

/-- Identify the preimage-open inclusion with its scheme base change.
Source: Stacks Project, Tag 09ZF, fourth proof paragraph; Sites, Tags 03CB and 03CC.
(blueprint: def-weil-pbc-gabber-h0-zariski-constructions). -/
noncomputable def gabberPreimageEtaleIso {S T : Scheme.{u}} (f : T ⟶ S) (W : S.Opens) :
    Scheme.Etale.mk (f ⁻¹ᵁ W).ι ≅
      (MorphismProperty.Over.pullback @Etale ⊤ f).obj (Scheme.Etale.mk W.ι) :=
  MorphismProperty.Over.isoMk
    ((pullbackRestrictIsoRestrict f W).symm ≪≫ pullbackSymmetry f W.ι)
    (by
      change ((pullbackRestrictIsoRestrict f W).inv ≫
        (pullbackSymmetry f W.ι).hom) ≫ pullback.snd W.ι f = _
      simp only [Category.assoc, pullbackSymmetry_hom_comp_snd,
        pullbackRestrictIsoRestrict_inv_fst]
      rfl)

/-- The first projection is the restricted morphism. Source: Stacks Project, Tag 01JR.
(blueprint: def-weil-pbc-gabber-h0-zariski-constructions). -/
@[simp]
theorem gabberPreimageEtaleIso_fst {S T : Scheme.{u}} (f : T ⟶ S) (W : S.Opens) :
    (gabberPreimageEtaleIso f W).hom.left ≫ pullback.fst W.ι f = f ∣_ W := by
  simp [gabberPreimageEtaleIso, morphismRestrict]

/-- Identify the identity etale object with the pullback of an identity.
Source: Stacks Project, Tag 09ZF, fourth proof paragraph; Sites, Tags 03CB and 03CC.
(blueprint: def-weil-pbc-gabber-h0-zariski-constructions). -/
noncomputable def gabberIdentityEtaleIso {S T : Scheme.{u}} (f : T ⟶ S) :
    Scheme.Etale.mk (𝟙 T) ≅
      (MorphismProperty.Over.pullback @Etale ⊤ f).obj (Scheme.Etale.mk (𝟙 S)) :=
  MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 S) f)).symm (by
    change _ ≫ pullback.snd (𝟙 S) f = 𝟙 T
    exact Iso.inv_hom_id _)

/-- Identify the top open with the identity etale object.
Source: Stacks Project, Tag 09ZF, fourth proof paragraph; Sites, Tags 03CB and 03CC.
(blueprint: def-weil-pbc-gabber-h0-zariski-constructions). -/
noncomputable def gabberTopEtaleIso (S : Scheme.{u}) :
    Scheme.Etale.mk (⊤ : S.Opens).ι ≅ Scheme.Etale.mk (𝟙 S) :=
  MorphismProperty.Over.isoMk S.topIso (by
    change (⊤ : S.Opens).ι ≫ 𝟙 S = (⊤ : S.Opens).ι
    exact Category.comp_id _)

/-- Identify the top open with the pullback of the identity etale object.
Source: Stacks Project, Tag 09ZF, fourth proof paragraph; Sites, Tags 03CB and 03CC.
(blueprint: def-weil-pbc-gabber-h0-zariski-constructions). -/
noncomputable def gabberTopPullbackIso {S T : Scheme.{u}} (f : T ⟶ S) :
    Scheme.Etale.mk (⊤ : T.Opens).ι ≅
      (MorphismProperty.Over.pullback @Etale ⊤ f).obj (Scheme.Etale.mk (𝟙 S)) :=
  gabberTopEtaleIso T ≪≫ gabberIdentityEtaleIso f

/-- Send a top-open section to the identity-pullback presentation of global sections.
Source: Stacks Project, Tag 09ZF, fourth proof paragraph; Sites, Tags 03CB and 03CC.
(blueprint: def-weil-pbc-gabber-h0-zariski-constructions). -/
noncomputable def gabberZariskiLift {X X' : Scheme.{u}} (h : X' ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    (gabberZariskiSheaf X' ((Scheme.etaleSetPullback h).obj F)).obj.obj
      (op (⊤ : X'.Opens)) →
    ((Scheme.etaleSetPullback h).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj (Scheme.Etale.mk (𝟙 X)))) :=
  fun s ↦ ((Scheme.etaleSetPullback h).obj F).obj.map (gabberTopPullbackIso h).inv.op s

/-- The canonical global-section isomorphism for the base-changed sheaf.
Source: Stacks Project, Tag 09ZF, fourth proof paragraph; Sites, Tags 03CB and 03CC.
(blueprint: def-weil-pbc-gabber-h0-zariski-constructions). -/
noncomputable def gabberZariskiSectionIso {X Z X' : Scheme.{u}}
    (i : Z ⟶ X) (h : X' ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    (gabberZariskiSheaf (pullback i h)
      ((Scheme.etaleSetPullback (pullback.snd i h)).obj
        ((Scheme.etaleSetPullback h).obj F))).obj.obj (op (⊤ : (pullback i h).Opens)) ≅
    ((Scheme.etaleSetPullback (pullback.fst i h ≫ i)).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst i h ≫ i)).obj
        (Scheme.Etale.mk (𝟙 X)))) := by
  let c := Classical.choose etaleSetInverseImageCompositionUnits.2.2
  let k := pullback.snd i h ≫ h
  let a := gabberTopEtaleIso (pullback i h) ≪≫
    gabberIdentityEtaleIso (pullback.snd i h) ≪≫
    (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd i h)).mapIso
      (gabberIdentityEtaleIso h)
  let K := (Scheme.etaleSetPullback (pullback.snd i h)).obj
    ((Scheme.etaleSetPullback h).obj F)
  let d := MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
    (pullback.snd i h) h
  let A := (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd i h)).obj
    ((MorphismProperty.Over.pullback @Etale ⊤ h).obj (Scheme.Etale.mk (𝟙 X)))
  exact K.obj.mapIso a.symm.op ≪≫
    (((sheafToPresheaf _ _).mapIso
      ((c X X' (pullback i h) h (pullback.snd i h)).app F)).app (op A)) ≪≫
    ((Scheme.etaleSetPullback k).obj F).obj.mapIso
      ((d.app (Scheme.Etale.mk (𝟙 X))).op) ≪≫
    eqToIso (congrArg
      (fun k : pullback i h ⟶ X ↦ ((Scheme.etaleSetPullback k).obj F).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
          (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := i) (g := h)).symm)

/-- The section function of the canonical comparison isomorphism.
Source: Stacks Project, Tag 09ZF, fourth proof paragraph; Sites, Tags 03CB and 03CC.
(blueprint: def-weil-pbc-gabber-h0-zariski-constructions). -/
noncomputable def gabberZariskiCompare {X Z X' : Scheme.{u}}
    (i : Z ⟶ X) (h : X' ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    (gabberZariskiSheaf (pullback i h)
      ((Scheme.etaleSetPullback (pullback.snd i h)).obj
        ((Scheme.etaleSetPullback h).obj F))).obj.obj (op (⊤ : (pullback i h).Opens)) →
    ((Scheme.etaleSetPullback (pullback.fst i h ≫ i)).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst i h ≫ i)).obj
        (Scheme.Etale.mk (𝟙 X)))) :=
  fun s ↦ (gabberZariskiSectionIso i h F).hom s

/-- The pointwise Kan extensions used for inverse image exist in Type (u + 1).
Source: Stacks Project, Tag 09ZF, fourth proof paragraph; Sites, Tags 03CB and 03CC.
(blueprint: def-weil-pbc-gabber-h0-zariski-constructions). -/
noncomputable instance gabberOpensKanExtension {S T : Scheme.{u}} (f : T ⟶ S)
    (P : S.Opensᵒᵖ ⥤ Type (u + 1)) :
    (Opens.map f.base).op.HasPointwiseLeftKanExtension P :=
  fun V ↦ @Types.hasColimit.{u, u + 1, u}
    (CostructuredArrow.{u, u, u, u} (Opens.map f.base).op V)
    inferInstance (small_succ.{u} _) (CostructuredArrow.proj (Opens.map f.base).op V ⋙ P)

/-- The constructed Zariski inverse image along a scheme morphism.
Source: Stacks Project, Tag 09ZF, fourth proof paragraph; Sites, Tags 03CB and 03CC.
(blueprint: def-weil-pbc-gabber-h0-zariski-constructions). -/
noncomputable def gabberZariskiPull {S T : Scheme.{u}} (f : T ⟶ S) :=
  Functor.sheafPullbackConstruction.sheafPullback (Opens.map f.base) (Type (u + 1))
    (Opens.grothendieckTopology S) (Opens.grothendieckTopology T)

/-- The component of the Zariski inverse-image unit on an open.
Source: Stacks Project, Tag 09ZF, fourth proof paragraph; Sites, Tags 03CB and 03CC.
(blueprint: def-weil-pbc-gabber-h0-zariski-constructions). -/
noncomputable def gabberZariskiUnit {S T : Scheme.{u}} (f : T ⟶ S)
    (G : TopCat.Sheaf (Type (u + 1)) S.toTopCat) (W : S.Opens) :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f.base) (Type (u + 1)) (Opens.grothendieckTopology S)
    (Opens.grothendieckTopology T)).unit.app G).hom.app (op W)

/-- The Zariski restriction of the etale pullback to Xprime.
Source: Stacks Project, Tag 09ZF, fourth proof paragraph; Sites, Tags 03CB and 03CC.
(blueprint: def-weil-pbc-gabber-h0-zariski-constructions). -/
noncomputable def gabberZariskiG {X X' : Scheme.{u}} (h : X' ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :=
  gabberZariskiSheaf X' ((Scheme.etaleSetPullback h).obj F)

/-- The Zariski restriction of the iterated etale pullback to Zprime.
Source: Stacks Project, Tag 09ZF, fourth proof paragraph; Sites, Tags 03CB and 03CC.
(blueprint: def-weil-pbc-gabber-h0-zariski-constructions). -/
noncomputable def gabberZariskiH {X Z X' : Scheme.{u}} (i : Z ⟶ X) (h : X' ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :=
  gabberZariskiSheaf (pullback i h) ((Scheme.etaleSetPullback (pullback.snd i h)).obj
    ((Scheme.etaleSetPullback h).obj F))

/-- Transport the pullback of t through the inverse section isomorphism.
Source: Stacks Project, Tag 09ZF, fourth proof paragraph; Sites, Tags 03CB and 03CC.
(blueprint: def-weil-pbc-gabber-h0-zariski-constructions). -/
noncomputable def gabberZariskiTargetSection {X Z X' : Scheme.{u}}
    (i : Z ⟶ X) (h : X' ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (t : ((Scheme.etaleSetPullback i).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj
        (Scheme.Etale.mk (𝟙 X))))) :=
  (gabberZariskiSectionIso i h F).inv
    (etaleSetDescentComparison i (pullback.fst i h) F (Scheme.Etale.mk (𝟙 X)) t)

/-- The componentwise condition identifying a comparison with the two units.
Source: Stacks Project, Tag 09ZF, fourth proof paragraph.
(blueprint: def-weil-pbc-gabber-h0-zariski-constructions). -/
def GabberZariskiUnitCompatible {X Z X' : Scheme.{u}}
    (i : Z ⟶ X) (h : X' ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (beta : (gabberZariskiPull (pullback.snd i h)).obj (gabberZariskiG h F) ⟶
      gabberZariskiH i h F) : Prop :=
  ∀ (W : X'.Opens) (s : (gabberZariskiG h F).obj.obj (op W)),
    beta.hom.app (op ((pullback.snd i h) ⁻¹ᵁ W))
      (gabberZariskiUnit (pullback.snd i h) (gabberZariskiG h F) W s) =
    ((Scheme.etaleSetPullback (pullback.snd i h)).obj
      ((Scheme.etaleSetPullback h).obj F)).obj.map
        (gabberPreimageEtaleIso (pullback.snd i h) W).hom.op
          (etaleSetDescentUnit (pullback.snd i h) ((Scheme.etaleSetPullback h).obj F)
            (Scheme.Etale.mk W.ι) s)

/-- Pull a representative to one open by the specified fibre-product map.
Source: Stacks Project, Tag 09ZF, fourth proof paragraph; Sites, Tags 03CB and 03CC.
(blueprint: def-weil-pbc-gabber-h0-zariski-constructions). -/
noncomputable def gabberLocalRepresentative {X U X' : Scheme.{u}}
    (q : U ⟶ X) [Etale q] (h : X' ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (s : F.obj.obj (op (Scheme.Etale.mk q))) (W : X'.Opens)
    (phi : W.toScheme ⟶ U) (hphi : phi ≫ q = W.ι ≫ h) :
    (gabberZariskiG h F).obj.obj (op W) :=
  ((Scheme.etaleSetPullback h).obj F).obj.map
    (MorphismProperty.Over.homMk (pullback.lift phi W.ι hphi)
      (pullback.lift_snd phi W.ι hphi) :
        Scheme.Etale.mk W.ι ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ h).obj (Scheme.Etale.mk q)).op
      (etaleSetDescentUnit h F (Scheme.Etale.mk q) s)

end AlgebraicGeometry
