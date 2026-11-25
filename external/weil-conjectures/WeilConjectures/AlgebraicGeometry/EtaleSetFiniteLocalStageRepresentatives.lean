/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetSheafComparison
public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
import WeilConjectures.AlgebraicGeometry.EtaleFiniteCoverFactorizationDescent
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageKanRepresentative
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Finite local stage representatives

Source: Stacks Project, Sites Tag 0A35 and Étale Cohomology Tag 09YQ.
(blueprint: lem-weil-pbc-sets-finite-local-stage-representatives).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private theorem finite_representatives
    {S T : Scheme.{u}} (g : T ⟶ S)
    (G : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (W : T.Etale) [CompactSpace W.left]
    (t : ((Scheme.etaleSetPullback g).obj G).obj.obj (op W)) :
    let B := MorphismProperty.Over.pullback @Etale ⊤ g
    let L := (Scheme.etaleSetPullback g).obj G
    let η := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous B
      (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
      (T.smallGrothendieckTopology @Etale)).unit.app G
    ∃ (n : ℕ) (V : Fin n → T.Etale) (a : ∀ q, V q ⟶ W)
      (U : Fin n → S.Etale) (b : ∀ q, V q ⟶ B.obj (U q))
      (z : ∀ q, G.obj.obj (op (U q))),
      Sieve.ofArrows V a ∈ T.smallEtaleTopology W ∧
      (∀ q, IsAffine (V q).left) ∧
      (∀ q, L.obj.map (a q).op t = L.obj.map (b q).op (η.hom.app (op (U q)) (z q))) := by
  classical
  dsimp only
  let B := MorphismProperty.Over.pullback @Etale ⊤ g
  let P := B.op.lan.obj G.obj
  let θ := toSheafify T.smallEtaleTopology P
  let R := Presheaf.imageSieve θ t
  have hR : R ∈ T.smallEtaleTopology W :=
    Presheaf.imageSieve_mem T.smallEtaleTopology θ t
  obtain ⟨n, V, a, ha, hV, hcover⟩ :=
    (AlgebraicGeometry.Etale.exists_affine_refinement _) hR
  have hrep (q : Fin n) : ∃ (U : S.Etale) (b : V q ⟶ B.obj U)
      (z : G.obj.obj (op U)),
      ((Scheme.etaleSetPullback g).obj G).obj.map (a q).op t =
        ((Scheme.etaleSetPullback g).obj G).obj.map b.op
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous B
            (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
            (T.smallGrothendieckTopology @Etale)).unit.app G).hom.app (op U) z) := by
    obtain ⟨p, hp⟩ := ha q
    obtain ⟨U, b, z, hz⟩ :=
      etaleInverseImageSectionDescription_representation S T g G (V q) p
    exact ⟨U, b, z, hp.symm.trans hz⟩
  choose U b z hz using hrep
  exact ⟨n, V, a, U, b, z, (Scheme.ofArrows_mem_smallEtaleTopology_iff a).mpr hcover,
    hV, hz⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparison_unit
    {R S T : Scheme.{u}} (h : T ⟶ S) (f : S ⟶ R) (k : T ⟶ R) (hk : h ≫ f = k)
    (G : Sheaf R.smallEtaleTopology (Type (u + 1))) (U : R.Etale)
    (s : G.obj.obj (op U)) :
    (etaleSetSheafComparison h f k hk G).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
        (R.smallGrothendieckTopology @Etale) (S.smallGrothendieckTopology @Etale)).unit.app
        G).hom.app (op U) s) =
    ((Scheme.etaleSetPullback k).obj G).obj.map
      (((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h f k hk.symm).app U).inv).op
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ k) (Type (u + 1))
        (R.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale)).unit.app
        G).hom.app (op U) s) := by
  subst k
  dsimp only [etaleSetSheafComparison, eqToHom_refl, Category.comp_id]
  exact (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).1 R S T f h G U s

/-- A limit section has finitely many local representatives from one stage.
They are not asserted to be compatible at that stage.

Source: Stacks Project, Sites Tag 0A35, equation-compute-pullback-to-limit,
existence of local representatives; Étale Cohomology Tag 09YQ.
(blueprint: lem-weil-pbc-sets-finite-local-stage-representatives).

Proof: Restrict to the cofinal tail above i₀. The inverse image is left Kan extension
followed by sheafification, so locally t is the image of an original section of G,
restricted along an arrow to a base-changed original object. Refine both these
original objects and the representing objects to affine étale objects; restrict
the original sections along their affine open covers. The test object at the limit is affine (the
cone projections are affine),
hence quasi-compact; choose a finite subcover. Descend these finitely many objects,
arrows, and their commutative triangles to a common stage by finite-presentation
object and arrow descent. Covering descent makes their arrows a cover of the
base change of W at a possibly later stage. Apply the stage inverse-image unit to
the original sections and restrict along the descended arrows to obtain s.
The composition-unit equations show their images under β are the restrictions
of t. Only the individual local representatives have been descended here: no
matching equations between different representatives are descended. An empty
cover gives an empty family, so the statement also includes an empty test object. -/
theorem etaleSet_finiteLocalStageRepresentatives
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W : (D.obj (op i₀)).FullAffineEtale)
    (t : ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W.obj))) :
    let H := fun j : Over (op i₀) ↦ (Scheme.etaleSetPullback (D.map j.hom)).obj G
    let L := (Scheme.etaleSetPullback (c.π.app (op i₀))).obj G
    let B := fun j : Over (op i₀) ↦ MorphismProperty.Over.pullback @Etale ⊤ (c.π.app j.left)
    let Y := fun j : Over (op i₀) ↦
      (MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj W.obj
    let e := fun j : Over (op i₀) ↦
      (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
        (c.π.app j.left) (D.map j.hom) (c.π.app (op i₀)) (c.w j.hom).symm).app W.obj
    let β := fun j : Over (op i₀) ↦
      etaleSetSheafComparison (c.π.app j.left) (D.map j.hom)
        (c.π.app (op i₀)) (c.w j.hom) G
    ∃ (j : Over (op i₀)) (n : ℕ) (V : Fin n → (D.obj j.left).Etale)
      (a : ∀ q, V q ⟶ Y j) (s : ∀ q, (H j).obj.obj (op (V q))),
      Sieve.ofArrows V a ∈ (D.obj j.left).smallEtaleTopology (Y j) ∧
      (∀ q, IsAffine (V q).left) ∧
      (∀ q, (β j).hom.app (op (V q)) (s q) =
        L.obj.map ((B j).map (a q) ≫ (e j).inv).op t) := by
  classical
  dsimp only
  let p := c.π.app (op i₀)
  let L := (Scheme.etaleSetPullback p).obj G
  let P := MorphismProperty.Over.pullback @Etale ⊤ p
  have : IsAffineHom p := isAffineHom_π_app D c hc (op i₀)
  have : IsAffine W.obj.left := W.property
  have : IsAffine ((𝟭 Scheme).obj W.obj.left) := W.property
  have : IsAffine (P.obj W.obj).left := by
    change IsAffine (pullback W.obj.hom p)
    have : IsAffineHom (pullback.fst W.obj.hom p) :=
      MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
    exact isAffine_of_isAffineHom (pullback.fst W.obj.hom p)
  obtain ⟨n, V, a, U, b, z, hcover, hV, hz⟩ :=
    finite_representatives p G (P.obj W.obj) t
  obtain ⟨j, Vj, aj, bj, d, hcoverj, hVj, haj, hbj⟩ :=
    etale_finiteCoverFactorizationDescent D c hc i₀ W n V a U b hcover hV
  let f := D.map j.hom
  let h := c.π.app j.left
  let F := MorphismProperty.Over.pullback @Etale ⊤ f
  let B := MorphismProperty.Over.pullback @Etale ⊤ h
  let H := (Scheme.etaleSetPullback f).obj G
  let η := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F
    (Type (u + 1)) ((D.obj (op i₀)).smallGrothendieckTopology @Etale)
    ((D.obj j.left).smallGrothendieckTopology @Etale)).unit.app G
  let β := etaleSetSheafComparison h f p (c.w j.hom) G
  let e := fun Z : (D.obj (op i₀)).Etale ↦
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      h f p (c.w j.hom).symm).app Z
  let s := fun q ↦ H.obj.map (bj q).op (η.hom.app (op (U q)) (z q))
  have : P.IsContinuous ((D.obj (op i₀)).smallGrothendieckTopology @Etale)
      (c.pt.smallGrothendieckTopology @Etale) := by
    dsimp [P]
    exact Scheme.isContinuous_overPullback @Etale @Etale le_rfl p
  refine ⟨j, n, Vj, aj, s, hcoverj, hVj, ?_⟩
  intro q
  change β.hom.app (op (Vj q)) (s q) = L.obj.map (B.map (aj q) ≫ (e W.obj).inv).op t
  have hu := comparison_unit h f p (c.w j.hom) G (U q) (z q)
  change β.hom.app (op (F.obj (U q))) (η.hom.app (op (U q)) (z q)) =
    L.obj.map ((e (U q)).inv).op
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous P (Type (u + 1))
        ((D.obj (op i₀)).smallGrothendieckTopology @Etale)
        (c.pt.smallGrothendieckTopology @Etale)).unit.app G).hom.app (op (U q)) (z q)) at hu
  calc
    β.hom.app (op (Vj q)) (s q) =
        L.obj.map (B.map (bj q)).op
          (β.hom.app (op (F.obj (U q))) (η.hom.app (op (U q)) (z q))) := by
      exact NatTrans.naturality_apply β.hom (bj q).op _
    _ = L.obj.map (B.map (bj q) ≫ (e (U q)).inv).op
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous P (Type (u + 1))
          ((D.obj (op i₀)).smallGrothendieckTopology @Etale)
          (c.pt.smallGrothendieckTopology @Etale)).unit.app G).hom.app (op (U q)) (z q)) := by
      rw [hu, op_comp, L.obj.map_comp]
      rfl
    _ = L.obj.map ((d q).hom ≫ b q).op
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous P (Type (u + 1))
          ((D.obj (op i₀)).smallGrothendieckTopology @Etale)
          (c.pt.smallGrothendieckTopology @Etale)).unit.app G).hom.app (op (U q)) (z q)) := by
      rw [hbj q]
    _ = L.obj.map ((d q).hom ≫ a q).op t := by
      rw [op_comp, op_comp, L.obj.map_comp, L.obj.map_comp]
      exact congrArg (L.obj.map (d q).hom.op) (hz q).symm
    _ = L.obj.map (B.map (aj q) ≫ (e W.obj).inv).op t := by rw [haj q]

end AlgebraicGeometry
