/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.AlgebraicGeometry.EtaleLimitOpenCohomologyCocone
import WeilConjectures.AlgebraicGeometry.TailOpenCohomologyLegNaturality
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Canonical cohomology cocone on inverse-image opens

Source: Stacks Project, Tags 09YQ and 01F7.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Canonical cohomology transition on the restricted stage opens.
Source: Stacks Project, Tags 09YQ and 01F7.
(blueprint: lem-weil-pbc-etale-limit-open-cohomology-cocone-degree). -/
noncomputable def tailOpenCohomologyMapDegree {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) {X : Scheme.{u}} {i₀ : I}
    (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (n : ℕ) {j k : Set.Ici i₀} (f : j ⟶ k) :
    AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ W j).ι).obj (F j.val)) n) ⟶
    AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ W k).ι).obj (F k.val)) n) :=
  AddCommGrpCat.ofHom (cohomologyMap (tailStageOpenMap D g₀ W f) _ n) ≫
    AddCommGrpCat.ofHom (Sheaf.H.map
      (openSquareCoefficient (D.map (homOfLE (show j.val ≤ k.val from f.le)).op)
        (tailStageOpen D g₀ W j).ι (tailStageOpen D g₀ W k).ι
        (tailStageOpenMap D g₀ W f)
        (by simp only [tailStageOpenMap, Scheme.Hom.resLE_comp_ι])
        (F j.val) (F k.val)
        (φ (homOfLE (show j.val ≤ k.val from f.le)))) n)

/-- Canonical cohomology leg from a stage open to the limit open.
Source: Stacks Project, Tags 09YQ and 01F7.
(blueprint: lem-weil-pbc-etale-limit-open-cohomology-cocone-degree). -/
noncomputable def tailOpenCohomologyLegDegree {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) {X : Scheme.{u}} {i₀ : I}
    (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (L : Cocone G) (n : ℕ) (j : Set.Ici i₀) :
    AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ W j).ι).obj (F j.val)) n) ⟶
    AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1}
        ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι).obj L.pt) n) :=
  AddCommGrpCat.ofHom (cohomologyMap (tailLimitOpenMap D c g₀ W j) _ n) ≫
    AddCommGrpCat.ofHom (Sheaf.H.map
      (openSquareCoefficient (c.π.app (op j.val)) (tailStageOpen D g₀ W j).ι
        ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι (tailLimitOpenMap D c g₀ W j)
        (by simp only [tailLimitOpenMap, Scheme.Hom.resLE_comp_ι]) (F j.val) L.pt
        ((eG j.val).inv ≫ L.ι.app j.val)) n)

/-- The canonical restricted cohomology arrows and legs form a diagram and cocone.

Source: Stacks Project, Tag 09YQ (coherent systems) and Tag 01F7 (functoriality).
(blueprint: lem-weil-pbc-etale-limit-open-cohomology-cocone-degree).

Proof: For each tail index j put W_j = (D(j -> i₀); g₀)^-1(W) and use
`tailStageOpenMap` for the restricted transitions. Pull F_j back along W_j.ι.
The coefficient transition is `openSquareCoefficient`: its first factor undoes
composition along the restricted transition and W_j.ι, its second factor composes
along W_k.ι and the original transition, and its last factor restricts φ.
The inverse-image identity and associativity coherences, applied to hidentity and
hcomposition, prove the restricted coefficient identity and composition equations.
Restrict G along the limit open inclusion, and whisker with the tail inclusion.
The original eG, the projection squares, and inverse-image composition identify
this diagram with the pullbacks of the restricted F_j. Naturality and hG give
its transition formula. Restrict and reindex L as a cocone; colimithood is not
needed here. Apply `etale_limit_canonical_cohomology_diagram` in degree n to
this restricted system. Its object identifications give eK and its arrow formula
is exactly `tailOpenCohomologyMapDegree`. Transport its cocone point using the
coefficient identification with the restriction of L.pt. The canonical leg
formula becomes `tailOpenCohomologyLegDegree`. No limit, compactness, affine transition,
or cohomology continuity assertion is used. For empty W all terms are the
cohomology of the empty schemes; for an identity singleton diagram these are
ordinary restriction maps. Arbitrary coefficients, including zero, are allowed. -/
theorem etale_limit_open_cohomology_cocone_degree
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G)
    {X : Scheme.{u}} (i₀ : I) (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens) (n : ℕ) :
    let BW := AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1}
        ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι).obj L.pt) n)
    ∃ (K : Set.Ici i₀ ⥤ AddCommGrpCat.{u + 1})
      (eK : ∀ j : Set.Ici i₀, K.obj j ≅ AddCommGrpCat.of (Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ W j).ι).obj (F j.val)) n)),
      (∀ (j k : Set.Ici i₀) (f : j ⟶ k), K.map f =
        (eK j).hom ≫ tailOpenCohomologyMapDegree D g₀ W F φ n f ≫ (eK k).inv) ∧
      ∃ (ι : K ⟶ (Functor.const (Set.Ici i₀)).obj BW),
        ∀ j, ι.app j = (eK j).hom ≫ tailOpenCohomologyLegDegree D c g₀ W F G eG L n j := by
  obtain ⟨hid, hcomp⟩ := tailOpenCohomologyArrow_laws D F φ hidentity hcomposition
    i₀ g₀ W n
  let K : Set.Ici i₀ ⥤ AddCommGrpCat.{u + 1} :=
    { obj := fun j ↦ AddCommGrpCat.of (Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ W j).ι).obj (F j.val)) n)
      map := fun f ↦ tailOpenCohomologyArrow D g₀ W F φ n f
      map_id := hid
      map_comp := fun f g ↦ hcomp _ _ _ f g }
  let ι : K ⟶ (Functor.const (Set.Ici i₀)).obj
      (AddCommGrpCat.of (Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1}
          ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι).obj L.pt) n)) :=
    { app := fun j ↦ tailOpenCohomologyCoconeLeg D c g₀ W F G eG L n j
      naturality := by
        intro j k f
        change tailOpenCohomologyArrow D g₀ W F φ n f ≫
          tailOpenCohomologyCoconeLeg D c g₀ W F G eG L n k =
          tailOpenCohomologyCoconeLeg D c g₀ W F G eG L n j ≫ 𝟙 _
        rw [Category.comp_id]
        exact tailOpenCohomologyCoconeLeg_naturality D c F φ G eG hG L i₀ g₀ W n j k f }
  refine ⟨K, fun _ ↦ Iso.refl _, ?_, ι, ?_⟩
  · intro j k f
    change tailOpenCohomologyArrow D g₀ W F φ n f =
      𝟙 _ ≫ tailOpenCohomologyMapDegree D g₀ W F φ n f ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
    rfl
  · intro j
    change tailOpenCohomologyCoconeLeg D c g₀ W F G eG L n j =
      𝟙 _ ≫ tailOpenCohomologyLegDegree D c g₀ W F G eG L n j
    rw [Category.id_comp]
    rfl


end AlgebraicGeometry.Etale
