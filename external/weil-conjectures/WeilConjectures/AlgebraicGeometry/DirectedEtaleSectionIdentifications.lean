/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparison
import WeilConjectures.AlgebraicGeometry.EtaleSetTerminalTransition
import WeilConjectures.AlgebraicGeometry.EtaleSetTerminalCone

/-! # Identification of the directed étale section comparisons

Source: Stacks Project, Tags 03S2, 03CB and 03CC, in the degree-zero route of Tag 09YQ.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Identify the section sets and maps on the upper tail of a chosen stage. This
comparison is independent of continuity: it requires neither qcqs stages, affine
transitions, directedness, nor a limiting cone.

Source: Stacks Project, Tag 03S2 (restriction along an étale morphism), Sites Tags
03CB and 03CC (inverse-image composition and units); the comparison step in Tag 09YQ.
(blueprint: lem-weil-pbc-directed-etale-section-identifications).

Proof: Put G equal to the inverse image of H on stage i₀, and W₀ equal to its
terminal étale object. For each j over i₀, the cone in the over-category gives
D(j.hom) followed by the structure map at i₀ equal to the structure map at j.
The unit-compatible composition isomorphism identifies the inverse image of G
along D(j.hom) with the inverse image of H along the latter structure map.
The base change of W₀ is canonically the terminal étale object at j: the
projection from the pullback of an identity is an isomorphism, whose inverse has
the identity and D(j.hom) as its projections. Evaluate the composition isomorphism
at this terminal object, then apply the étale-restriction isomorphism. Invert this
composite to obtain a_j. The same composition calculation for the cone leg at i₀,
using h i₀, and the terminal-object pullback isomorphism gives l at the limit;
no étale hypothesis on p or the limit leg is used here.
For a transition k → j, expand the section comparison. Unit naturality and the
composition unit equation move a pulled-back section through this composite.
The restriction unit equation changes it to H on the opposite transition map.
The two fibre-product pasting maps coincide because their first and second
projections coincide. This proves the transition equation. Apply that calculation
to a cone leg: the first projection is c_j and the second is the identity, so the
resulting map is precisely the diagonal map stipulated in hν. This proves the
component equation. A singleton diagram reduces to the restriction isomorphism;
empty stage schemes cause no problem because all constructions are categorical
isomorphisms and the sheaf axiom gives a singleton section set there. -/
theorem directedEtaleSectionIdentifications
    {I : Type u} [Preorder I]
    {R : Scheme.{u}} (B : Iᵒᵖ ⥤ R.Etale)
    (c : Cone (B ⋙ Scheme.Etale.forget R ⋙ Over.forget R))
    (p : c.pt ⟶ R) (h : ∀ i, c.π.app i ≫ (B.obj i).hom = p)
    (H : Sheaf R.smallEtaleTopology (Type (u + 1)))
    (i₀ : I)
    (ν : B.op ⋙ H.obj ⟶ (Functor.const Iᵒᵖᵒᵖ).obj
      (((Scheme.etaleSetPullback p).obj H).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt)))))
    (hν : ∀ i, ν.app i =
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ p) (Type (u + 1))
        (R.smallGrothendieckTopology @Etale)
        (c.pt.smallGrothendieckTopology @Etale)).unit.app H).hom.app
          (op (B.obj i.unop))) ≫
        ((Scheme.etaleSetPullback p).obj H).obj.map
          (MorphismProperty.Over.homMk
            (B := (MorphismProperty.Over.pullback @Etale ⊤ p).obj (B.obj i.unop))
            (pullback.lift (c.π.app i.unop) (𝟙 _) (by simpa using h i.unop))
            (pullback.lift_snd _ _ _)).op) :
    let D := B ⋙ Scheme.Etale.forget R ⋙ Over.forget R
    let G := (Scheme.etaleSetPullback (B.obj (op i₀)).hom).obj H
    let W₀ := Scheme.Etale.mk (𝟙 (D.obj (op i₀)))
    ∃ (a : ∀ j : Over (op i₀), H.obj.obj (op (B.obj j.left)) ≅
        ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj W₀)))
      (l : ((Scheme.etaleSetPullback p).obj H).obj.obj
          (op (Scheme.Etale.mk (𝟙 c.pt))) ≅
        ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G).obj.obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W₀))),
      (∀ (j k : Over (op i₀)) (f : k ⟶ j),
        H.obj.map (B.map f.left).op ≫ (a k).hom =
          (a j).hom ≫ etaleSetSectionComparison
            (D.map f.left) (D.map j.hom) (D.map k.hom)
            ((D.map_comp f.left j.hom).symm.trans
              (congrArg (fun t : k.left ⟶ op i₀ ↦ D.map t) f.w)) G W₀) ∧
      (∀ j : Over (op i₀),
        ν.app (op j.left) ≫ l.hom = (a j).hom ≫
          etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
            (c.π.app (op i₀)) (c.w j.hom) G W₀)  := by
  let D := B ⋙ Scheme.Etale.forget R ⋙ Over.forget R
  let W := B.obj (op i₀)
  let a := fun j : Over (op i₀) ↦
    etaleSetTerminalRestriction H (B.obj j.left) ≪≫
      etaleSetTerminalTransport W.hom (D.map j.hom) (B.obj j.left).hom
        (MorphismProperty.Over.w (B.map j.hom)) H
  let l := etaleSetTerminalTransport W.hom (c.π.app (op i₀)) p (h (op i₀)) H
  refine ⟨a, l, ?_, ?_⟩
  · intro j k f
    exact etaleSetTerminalTransition H (B.obj j.left) (B.obj k.left) W
      (B.map f.left) (B.map j.hom) (B.map k.hom) _
  · intro j
    rw [hν (op j.left)]
    exact etaleSetTerminalCone H (B.obj j.left) W (B.map j.hom) p
      (c.π.app j.left) (c.π.app (op i₀)) (c.w j.hom) (h j.left) (h (op i₀))

end AlgebraicGeometry
