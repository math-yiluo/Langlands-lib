/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveSetDescentInjective
import WeilConjectures.AlgebraicGeometry.GabberH0ZariskiRepresentativeEquation
import WeilConjectures.AlgebraicGeometry.GabberH0ZariskiTopUnitEquation

/-! # Local data for Zariski gluing

Source: Stacks Project, Tag 09ZF, fourth proof paragraph.
(blueprint: lem-weil-pbc-gabber-h0-zariski-local-data).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

private theorem sectionIso_apply_inv {A B : Type (u + 1)} (e : A ≅ B) (x : B) :
    e.hom (e.inv x) = x := by
  exact ConcreteCategory.congr_hom e.inv_hom_id x

/-- Restrict the pulled-back etale sheaves to opens and transport the representative
and unit equations to these restrictions. This gives local lifts, before gluing.
Source: Stacks Project, Tag 09ZF, fourth proof paragraph.
(blueprint: lem-weil-pbc-gabber-h0-zariski-local-data).

Proof: Put F' = h^*F and i' = pullback.snd i h. Restrict F' and (i')^*F'
along the open-subscheme inclusions to obtain G and H; continuity of these
inclusions makes them sheaves. Their underlying presheaves give eX and eZ.
The preimage of an open under i' is its fibre product with Z', giving a and
its first-projection equation. Identify the top-open object with the identity
etale object, and the latter's pullback with the identity object on the source.
These identifications give lift. Apply the same identifications to H and then
the composition isomorphism for h followed by i', transported along the
pullback square, to obtain e. Its inverse transports the pullback of t to tH.
The defining composition comparison gives the displayed equation for e tH.

Now let beta satisfy the displayed comparison-unit equation. For every a,
take V a to be the preimage of W a under i'. Pull s along the map phi a into
F' on W a: the fibre-product map has first projection phi a and second
projection the open inclusion, because hphi is their commuting equation.
Send this section through the Zariski inverse-image unit, obtaining sf a on
V a. The assumed unit equation for beta identifies its image with the etale
pullback. Naturality of the etale unit, hs, and unit-compatible composition
identify that image with the restriction of tH. Preimages of the W a cover
Z', giving the cover equation. Applying the same beta equation at the top
open, then the composition comparison, gives the final unit equation, with
its transport exactly pullback.condition. No injectivity or gluing is used
here. For an empty index type hW forces X' empty, hence Z' empty, and the
empty cover and unique empty sections give the same conclusions. -/
theorem gabber_h0_zariski_local_data
    {X Z U X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (q : U ⟶ X) [Etale q] (h : X' ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (t : ((Scheme.etaleSetPullback i).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj (Scheme.Etale.mk (𝟙 X)))))
    (s : F.obj.obj (op (Scheme.Etale.mk q)))
    (hs : etaleSetDescentUnit i F (Scheme.Etale.mk q) s =
      ((Scheme.etaleSetPullback i).obj F).obj.map
        ((MorphismProperty.Over.pullback @Etale ⊤ i).map
          (MorphismProperty.Over.homMk q (Category.comp_id q) :
            Scheme.Etale.mk q ⟶ Scheme.Etale.mk (𝟙 X))).op t)
    (J : Type) (W : J → X'.Opens) (phi : ∀ a, (W a).toScheme ⟶ U)
    (hW : ⨆ a, W a = ⊤) (hphi : ∀ a, phi a ≫ q = (W a).ι ≫ h) :
    let b : CategoryTheory.Functor.{u, u, u, u}
        X'.Opens (pullback i h : Scheme.{u}).Opens :=
      Opens.map ((pullback.snd i h : (pullback i h : Scheme.{u}) ⟶ X').base)
    letI : ∀ P : X'.Opensᵒᵖ ⥤ Type (u + 1), b.op.HasPointwiseLeftKanExtension P :=
      fun P V ↦
        @Types.hasColimit.{u, u + 1, u} (CostructuredArrow.{u, u, u, u} b.op V)
          inferInstance (small_succ.{u} _) (CostructuredArrow.proj b.op V ⋙ P)
    ∃ (G : TopCat.Sheaf (Type (u + 1)) X'.toTopCat)
      (lift : G.obj.obj (op (⊤ : X'.Opens)) →
        ((Scheme.etaleSetPullback h).obj F).obj.obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj
            (Scheme.Etale.mk (𝟙 X)))))
      (H : TopCat.Sheaf (Type (u + 1)) (pullback i h : Scheme.{u}).toTopCat)
      (eX : G.obj ≅
      (MorphismProperty.Comma.lift (P := @Etale) (Q := ⊤) (W := ⊤)
        X'.restrictFunctor (fun U => (inferInstance : Etale U.ι))
        (fun _ => trivial)
        (fun _ => trivial)).op ⋙ ((Scheme.etaleSetPullback h).obj F).obj)
      (eZ : H.obj ≅
      (MorphismProperty.Comma.lift (P := @Etale) (Q := ⊤) (W := ⊤)
        (pullback i h : Scheme.{u}).restrictFunctor (fun U => (inferInstance : Etale U.ι))
        (fun _ => trivial)
        (fun _ => trivial)).op ⋙
      ((Functor.sheafPullbackConstruction.sheafPullback
        (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd i h)) (Type (u + 1))
        (X'.smallGrothendieckTopology @Etale)
        ((pullback i h : Scheme.{u}).smallGrothendieckTopology @Etale)).obj
          ((Scheme.etaleSetPullback h).obj F)).obj)
      (a : ∀ W : X'.Opens, Scheme.Etale.mk ((pullback.snd i h) ⁻¹ᵁ W).ι ≅
      (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd i h)).obj (Scheme.Etale.mk W.ι)),
      (∀ W : X'.Opens,
        (a W).hom.left ≫ pullback.fst W.ι (pullback.snd i h) =
          (pullback.snd i h) ∣_ W) ∧
      ∃ (e : H.obj.obj (op (⊤ : (pullback i h : Scheme.{u}).Opens)) →
        ((Scheme.etaleSetPullback (pullback.fst i h ≫ i)).obj F).obj.obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst i h ≫ i)).obj
            (Scheme.Etale.mk (𝟙 X)))))
      (tH : H.obj.obj (op (⊤ : (pullback i h : Scheme.{u}).Opens))),
      e tH = etaleSetDescentComparison i (pullback.fst i h) F (Scheme.Etale.mk (𝟙 X)) t ∧
      ∀ (beta : ((Functor.sheafPullbackConstruction.sheafPullback b (Type (u + 1))
          (Opens.grothendieckTopology X')
          (Opens.grothendieckTopology (pullback i h : Scheme.{u}))).obj G) ⟶ H),
        (∀ (W : X'.Opens) (s : G.obj.obj (op W)),
        beta.hom.app (op ((pullback.snd i h) ⁻¹ᵁ W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (Opens.map (pullback.snd i h).base) (Type (u + 1))
            (Opens.grothendieckTopology X'.carrier)
            (Opens.grothendieckTopology (pullback i h : Scheme.{u}).carrier)).unit.app G).hom.app
              (op W) s) =
        eZ.inv.app (op ((pullback.snd i h) ⁻¹ᵁ W))
          (((Functor.sheafPullbackConstruction.sheafPullback
            (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd i h)) (Type (u + 1))
            (X'.smallGrothendieckTopology @Etale)
            ((pullback i h : Scheme.{u}).smallGrothendieckTopology @Etale)).obj
          ((Scheme.etaleSetPullback h).obj F)).obj.map (a W).hom.op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd i h)) (Type (u + 1))
              (X'.smallGrothendieckTopology @Etale)
              ((pullback i h : Scheme.{u}).smallGrothendieckTopology @Etale)).unit.app
                ((Scheme.etaleSetPullback h).obj F)).hom.app
                (op (Scheme.Etale.mk W.ι)) (eX.hom.app (op W) s)))) →
      (∃ (V : J → (pullback i h : Scheme.{u}).Opens)
        (sf : ∀ a, ((Functor.sheafPullbackConstruction.sheafPullback b (Type (u + 1))
          (Opens.grothendieckTopology X')
          (Opens.grothendieckTopology (pullback i h : Scheme.{u}))).obj G).obj.obj (op (V a))),
        (⨆ a, V a = ⊤) ∧ ∀ a,
          beta.hom.app (op (V a)) (sf a) =
            H.obj.map (homOfLE (show V a ≤ ⊤ from le_top)).op tH) ∧
      (∀ a : G.obj.obj (op (⊤ : X'.Opens)),
        (e ∘ beta.hom.app (op (⊤ : (pullback i h : Scheme.{u}).Opens)))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            b (Type (u + 1)) (Opens.grothendieckTopology X')
            (Opens.grothendieckTopology (pullback i h : Scheme.{u}))).unit.app G).hom.app
              (op (⊤ : X'.Opens)) a) =
          eqToHom (congrArg
            (fun k : pullback i h ⟶ X ↦ ((Scheme.etaleSetPullback k).obj F).obj.obj
              (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
                (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := i) (g := h)).symm)
            (etaleSetDescentComparison h (pullback.snd i h) F
              (Scheme.Etale.mk (𝟙 X)) (lift a))) := by
  dsimp only
  refine ⟨gabberZariskiG h F, gabberZariskiLift h F, gabberZariskiH i h F,
    Iso.refl _, Iso.refl _, gabberPreimageEtaleIso (pullback.snd i h), ?_,
    gabberZariskiCompare i h F, gabberZariskiTargetSection i h F t, ?_, ?_⟩
  · exact gabberPreimageEtaleIso_fst (pullback.snd i h)
  · exact sectionIso_apply_inv (gabberZariskiSectionIso i h F) _
  · intro beta hbeta
    have hb : GabberZariskiUnitCompatible i h F beta := hbeta
    constructor
    · refine ⟨fun a ↦ (pullback.snd i h) ⁻¹ᵁ W a,
        fun a ↦ gabberZariskiUnit (pullback.snd i h) (gabberZariskiG h F) (W a)
          (gabberLocalRepresentative q h F s (W a) (phi a) (hphi a)), ?_, ?_⟩
      · apply Opens.ext
        ext x
        change (x ∈ ⨆ a, (pullback.snd i h) ⁻¹ᵁ W a) ↔ x ∈ (⊤ : (pullback i h).Opens)
        simp only [Opens.mem_iSup, Scheme.Hom.mem_preimage, Opens.mem_top, iff_true]
        have hx : (pullback.snd i h) x ∈ ⨆ a, W a := by rw [hW]; trivial
        exact Opens.mem_iSup.mp hx
      · intro a
        exact gabber_h0_zariski_representative_equation i q h F t s hs
          (W a) (phi a) (hphi a) beta hb
    · exact gabber_h0_zariski_top_unit_equation i h F beta hb

end AlgebraicGeometry
