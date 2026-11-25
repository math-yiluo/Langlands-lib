/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveSetDescentInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveSetDescentGermLifts

/-! # Compatible finite-descent sections lift étale locally

Source: Stacks Project, Étale Cohomology, Remark 09Z3 and Lemma 09Z2.
(blueprint: lem-weil-pbc-sets-finite-descent-local-lifts).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem imageSieve_mem_of_geometric_germ_lifts
    {X : Scheme.{u}} {F H : Sheaf X.smallEtaleTopology (Type (u + 1))}
    (η : F ⟶ H) (s : H.obj.obj (op (Scheme.Etale.mk (𝟙 X))))
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (x : Spec (.of Ω) ⟶ X)
      (z : (Scheme.pointSmallEtale x).fiber.obj (Scheme.Etale.mk (𝟙 X))),
      ∃ a : (Scheme.pointSmallEtale x).sheafFiber.obj F,
        (Scheme.pointSmallEtale x).sheafFiber.map η a =
          (Scheme.pointSmallEtale x).toPresheafFiber
            (Scheme.Etale.mk (𝟙 X)) z H.obj s) :
    Presheaf.imageSieve η.hom s ∈ X.smallEtaleTopology (Scheme.Etale.mk (𝟙 X)) := by
  classical
  let U := Scheme.Etale.mk (𝟙 X)
  have local_lift (v : X) : ∃ (V : X.Etale) (m : V ⟶ U) (w : V.left),
      m.left w = v ∧ ∃ a : F.obj.obj (op V), η.hom.app (op V) a = H.obj.map m.op s := by
    let Ω := AlgebraicClosure (X.residueField v)
    let x : Spec (.of Ω) ⟶ X := (Scheme.SpecToEquivOfField Ω X).symm
      ⟨v, CommRingCat.ofHom (algebraMap (X.residueField v) Ω)⟩
    let z : (Scheme.pointSmallEtale x).fiber.obj U := Over.homMk x (by simp [U])
    obtain ⟨a, ha⟩ := h Ω x z
    obtain ⟨V, w, b, rfl⟩ :=
      (Scheme.pointSmallEtale x).toPresheafFiber_jointly_surjective (P := F.obj) a
    let m : V ⟶ U := MorphismProperty.Over.homMk V.hom (by simp [U])
    have hw : (Scheme.pointSmallEtale x).fiber.map m w = z := by
      apply Over.OverMorphism.ext
      simp [Scheme.pointSmallEtale, Scheme.Etale.forget, m, z, U]
    change (Scheme.pointSmallEtale x).presheafFiber.map η.hom
      ((Scheme.pointSmallEtale x).toPresheafFiber V w F.obj b) = _ at ha
    have he : (Scheme.pointSmallEtale x).toPresheafFiber V w H.obj
        (η.hom.app (op V) b) =
        (Scheme.pointSmallEtale x).toPresheafFiber V w H.obj (H.obj.map m.op s) := by
      rw [← GrothendieckTopology.Point.toPresheafFiber_naturality_apply]
      rw [ha, GrothendieckTopology.Point.toPresheafFiber_w_apply, hw]
    obtain ⟨W, r, t, ht, heq⟩ :=
      ((Scheme.pointSmallEtale x).toPresheafFiber_eq_iff'
        (A := Type (u + 1)) (P := H.obj) V w _ _).1 he
    refine ⟨W, r ≫ m, t.left (default : Spec (.of Ω)), ?_, F.obj.map r.op b, ?_⟩
    · have hv := congrArg (fun z ↦ z.left (default : Spec (.of Ω)))
        (show (Scheme.pointSmallEtale x).fiber.map (r ≫ m) t = z by
          rw [Functor.map_comp, types_comp_apply, ht, hw])
      change (r ≫ m).left (t.left (default : Spec (.of Ω))) = x default at hv
      refine hv.trans ?_
      change X.fromSpecResidueField v _ = v
      exact Scheme.fromSpecResidueField_apply _ _
    · rw [NatTrans.naturality_apply]
      rw [heq]
      simp only [op_comp, H.obj.map_comp, types_comp_apply]
  choose V m w hw a ha using local_lift
  have hcover : Sieve.ofArrows V m ∈ X.smallEtaleTopology U := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    ext v
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨v, w v, hw v⟩
  apply X.smallEtaleTopology.superset_covering _ hcover
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro v
  exact ⟨a v, ha v⟩


/-- A compatible section belongs étale locally to the image of the adjunction unit.
Source: Stacks Project, Étale Cohomology, Remark 09Z3, proved as Lemma 09Z2
using Proposition 03QP (1) and Lemma 03Q1 (3).
(blueprint: lem-weil-pbc-sets-finite-descent-local-lifts).

Proof: Put A = f_* f⁻¹G and D = X' ×_X X', with h = p₁ ≫ f = p₂ ≫ f.
The projections and h are finite by base change and composition. For a geometric
point x of X, the set P of its lifts to X' with the same algebraically closed
field is nonempty by surjectivity and finite geometric-point lifting. Lifts to D
are pairs of lifts to X'. Finite pushforward stalks identify A_x with the product
of the inverse-image stalks over P; the germ-compatible inverse-image bijections
identify these stalks with G_x. They identify the unit with the diagonal. The
composition-unit formula, tested on germs of unit-pulled-back sections, identifies
the two comparison maps on stalks with the two coordinate projections indexed
by P × P. Such germs generate each inverse-image stalk by its germ bijection,
so this calculation determines the comparison maps on all germs. Compatibility
of s' therefore makes its germ a constant P-indexed family. Choose a lift in P;
its coordinate supplies a germ in G_x mapping to the germ of s'. Represent this
germ by a section over a pointed étale neighbourhood. Equality in the filtered
colimit defining A_x is witnessed after an étale refinement, so on that refinement
the restriction of s' is the unit of this section. These refinements contain a
point above every point of X, choosing an algebraic closure of each residue field,
and hence cover X. Their arrows belong to the image sieve, which consequently
covers X. For empty X the empty sieve covers X, giving the same conclusion.
This statement supplies local existence only; agreement and global gluing are
proved separately in the equalizer module. -/
theorem finiteSurjectiveSetDescent_compatible_locally_lifts
    {X X' : Scheme.{u}} (f : X' ⟶ X) [IsFinite f] [Surjective f]
    (G : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    ∀ s' : ((Scheme.etaleSetPullback f).obj G).obj.obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
            (Scheme.Etale.mk (𝟙 X)))),
        etaleSetDescentComparison f (pullback.fst f f) G (Scheme.Etale.mk (𝟙 X)) s' =
          eqToHom (congrArg
            (fun k : pullback f f ⟶ X ↦ ((Scheme.etaleSetPullback k).obj G).obj.obj
              (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
                (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := f) (g := f)).symm)
            (etaleSetDescentComparison f (pullback.snd f f) G
              (Scheme.Etale.mk (𝟙 X)) s') →
          Presheaf.imageSieve
            ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
              (X.smallGrothendieckTopology @Etale)
              (X'.smallGrothendieckTopology @Etale)).unit.app G).hom s' ∈
            X.smallEtaleTopology (Scheme.Etale.mk (𝟙 X)) := by
  intro s' hs'
  apply imageSieve_mem_of_geometric_germ_lifts
  exact finiteSurjectiveSetDescent_compatible_germ_lifts f G s' hs'

end AlgebraicGeometry
