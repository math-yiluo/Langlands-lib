/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetSheafComparison
public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpen
import WeilConjectures.AlgebraicGeometry.EtaleSetCartesianUnitEquality
import WeilConjectures.AlgebraicGeometry.EtalePairRestrictionDetection
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Eventual compatibility of finitely many stage sections

Source: Stacks Project, Sites Tag 0A35; Étale Cohomology Tag 0EYL.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry



set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparison_equal_open
    {R S : Scheme.{u}} (f : S ⟶ R)
    (G : Sheaf R.smallEtaleTopology (Type (u + 1))) (Q : S.Etale)
    (s t : ((Scheme.etaleSetPullback f).obj G).obj.obj (op Q)) :
    ∃ U : Q.left.Opens, ∀ (T : Scheme.{u}) (h : T ⟶ S)
      (k : T ⟶ R) (hk : h ≫ f = k),
      (etaleSetSheafComparison h f k hk G).hom.app (op Q) s =
        (etaleSetSheafComparison h f k hk G).hom.app (op Q) t ↔
      (pullback.fst Q.hom h) ⁻¹ᵁ U = ⊤ := by
  classical
  let F := (Scheme.etaleSetPullback f).obj G
  obtain ⟨U, hU, _⟩ := existsUnique_etaleSections_equal_open S F Q s t
  refine ⟨U, ?_⟩
  intro T h k hk
  subst k
  let A := (MorphismProperty.Over.pullback @Etale ⊤ h).obj Q
  let p : A.left ⟶ Q.left := pullback.fst Q.hom h
  let η := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
    (S.smallGrothendieckTopology @Etale)
    (T.smallGrothendieckTopology @Etale)).unit.app F).hom.app (op Q)
  let γ := ((Classical.choose etaleSetInverseImageCompositionUnits.2.2 R S T f h).hom.app
    G).hom.app (op A)
  have hγ : Function.Injective γ := CategoryTheory.injective_of_mono γ
  have hcomparison :
      (etaleSetSheafComparison h f (h ≫ f) rfl G).hom.app (op Q) s =
        (etaleSetSheafComparison h f (h ≫ f) rfl G).hom.app (op Q) t ↔ η s = η t := by
    dsimp only [etaleSetSheafComparison, eqToHom_refl, Category.comp_id]
    change γ (η s) = γ (η t) ↔ η s = η t
    exact ⟨fun heq ↦ hγ heq, fun heq ↦ congrArg γ heq⟩
  have hunit := etaleSetCartesianUnit_eq_iff h F Q A (Iso.refl _) p
    (by change (𝟙 _) ≫ _ = _; simp [p]) s t
  have hopen : (∃ b : A.left ⟶ U.toScheme, b ≫ U.ι = p) ↔ p ⁻¹ᵁ U = ⊤ := by
    constructor
    · rintro ⟨b, hb⟩
      apply top_unique
      intro x _
      change p x ∈ U
      have hx := congrArg (fun a : A.left ⟶ Q.left ↦ a x) hb
      rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] at hx
      rw [← hx]
      exact (b x).property
    · intro hall
      refine ⟨IsOpenImmersion.lift U.ι p ?_, IsOpenImmersion.lift_fac _ _ _⟩
      rw [Scheme.Opens.range_ι]
      rintro x ⟨y, rfl⟩
      have hy : y ∈ p ⁻¹ᵁ U := by rw [hall]; trivial
      exact hy
  exact hcomparison.trans (hunit.trans ((hU A.left p).symm.trans hopen))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparison_eventually_equal
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (j : Over (op i₀)) (Q : (D.obj j.left).Etale) [QuasiCompact Q.hom]
    (s t : ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.obj (op Q))
    (hst : (etaleSetSheafComparison (c.π.app j.left) (D.map j.hom)
        (c.π.app (op i₀)) (c.w j.hom) G).hom.app (op Q) s =
      (etaleSetSheafComparison (c.π.app j.left) (D.map j.hom)
        (c.π.app (op i₀)) (c.w j.hom) G).hom.app (op Q) t) :
    ∃ (l : Over (op i₀)) (d : l ⟶ j),
      ∀ (k : Over (op i₀)) (e : k ⟶ l),
        (etaleSetSheafComparison (D.map (e ≫ d).left) (D.map j.hom) (D.map k.hom)
          ((D.map_comp (e ≫ d).left j.hom).symm.trans
            (congrArg (fun z : k.left ⟶ op i₀ ↦ D.map z) (e ≫ d).w)) G).hom.app
              (op Q) s =
        (etaleSetSheafComparison (D.map (e ≫ d).left) (D.map j.hom) (D.map k.hom)
          ((D.map_comp (e ≫ d).left j.hom).symm.trans
            (congrArg (fun z : k.left ⟶ op i₀ ↦ D.map z) (e ≫ d).w)) G).hom.app
              (op Q) t := by
  classical
  let B := Over.forget j.left ⋙ D
  let b := c.whisker (Over.forget j.left)
  have hb : IsLimit b :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget j.left) c).symm hc
  let : IsConnected (Over j.left) := IsCofiltered.isConnected _
  let E : Over j.left ⥤ Scheme.{u} :=
    { obj := fun k ↦ pullback Q.hom (D.map k.hom)
      map := fun {k l} a ↦ pullback.map _ _ _ _ (𝟙 Q.left) (D.map a.left) (𝟙 _)
        (by simp) (by simp only [Category.comp_id, ← D.map_comp, a.w])
      map_id := fun k ↦ by apply pullback.hom_ext <;> simp
      map_comp := fun a a' ↦ by apply pullback.hom_ext <;> simp }
  let q : Cone E :=
    { pt := pullback Q.hom (c.π.app j.left)
      π :=
        { app := fun k ↦ pullback.map _ _ _ _ (𝟙 Q.left) (c.π.app k.left) (𝟙 _)
            (by simp) (by simp)
          naturality := fun k l a ↦ by apply pullback.hom_ext <;> simp [E] } }
  let β : E ⟶ B :=
    { app := fun k ↦ pullback.snd Q.hom (D.map k.hom)
      naturality := fun k l a ↦ by simp [E, B] }
  have hq : IsLimit q :=
    isLimitOfIsPullbackOfIsConnected β q b
      { hom := pullback.snd Q.hom (c.π.app j.left)
        w := fun k ↦ by simp [q, β, b] }
      (fun k ↦ isPullback_pullback_map Q.hom (c.π.app j.left)
        (D.map k.hom) (c.π.app k.left) (c.w k.hom)) hb
  let : ∀ k, CompactSpace (E.obj k) := fun k ↦ by dsimp [E]; infer_instance
  let : ∀ {k l} (a : k ⟶ l), IsAffineHom (E.map a) := fun {k l} a ↦
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (isPullback_pullback_map Q.hom (D.map k.hom) (D.map l.hom)
        (D.map a.left) (by rw [← D.map_comp, a.w])).flip inferInstance
  obtain ⟨U, hU⟩ := comparison_equal_open (D.map j.hom) G Q s t
  have hlimit : (pullback.fst Q.hom (c.π.app j.left)) ⁻¹ᵁ U = ⊤ :=
    (hU c.pt (c.π.app j.left) (c.π.app (op i₀)) (c.w j.hom)).mp hst
  let o : Over j.left := Over.mk (𝟙 j.left)
  let U₀ : (E.obj o).Opens := (pullback.fst Q.hom (D.map o.hom)) ⁻¹ᵁ U
  have hlimit₀ : q.π.app o ⁻¹ᵁ U₀ = ⊤ := by
    simpa [U₀, q, ← Scheme.Hom.comp_preimage] using hlimit
  obtain ⟨l, a, ha⟩ := exists_map_eq_top E q hq U₀ hlimit₀
  have hl : (pullback.fst Q.hom (D.map l.hom)) ⁻¹ᵁ U = ⊤ := by
    simpa [U₀, E, ← Scheme.Hom.comp_preimage] using ha
  let L : Over (op i₀) := Over.mk (l.hom ≫ j.hom)
  let d : L ⟶ j := Over.homMk l.hom
  refine ⟨L, d, ?_⟩
  intro k e
  apply (hU (D.obj k.left) (D.map (e ≫ d).left) (D.map k.hom) _).mpr
  let v := pullback.map Q.hom (D.map (e ≫ d).left) Q.hom (D.map l.hom)
    (𝟙 Q.left) (D.map e.left) (𝟙 _)
    (by simp) (by simp [d, Over.comp_left, D.map_comp])
  have hh := congrArg (fun Z ↦ v ⁻¹ᵁ Z) hl
  simpa [v, ← Scheme.Hom.comp_preimage] using hh

-- The unchanged signature names V' only as an implicit object family.
set_option linter.unusedVariables false in
/-- Finitely many affine local sections with a common image at the limit become
compatible at some later stage. No covering hypothesis or covering conclusion is needed.

Source: Stacks Project, Sites Tag 0A35, equation-compute-pullback-to-limit
and its finite-matching argument; Étale Cohomology Tag 0EYL.
(blueprint: lem-weil-pbc-sets-eventual-local-stage-matching-compatibility).

Proof: The base change Y_j of W is affine, since W is affine and the transition
map is affine. For each ordered pair q,q', form P = V_q ×_{Y_j} V_q'. This is
an affine étale object over D(j). Restrict s_q and s_q' to P. Naturality of the
sheaf comparison and the given equations with t show that these two sections
have the same image on the base change of P to the limit.
Restrict the original inverse system to stages above j; its limit is still c.pt.
Apply the affine-site colimit presentation (0EYL), the equivalence between full
and affine étale sheaves, and the section formula of 0A35 to the sheaf H_j and
object P. The two equal limit sections are equal in this filtered colimit, so
they become equal at one later stage. Unit-compatible inverse-image composition
identifies these colimit transition maps with the comparisons in the statement.
There are finitely many pairs. Directedness gives one common later stage for
all their equality witnesses; transporting equalities to it preserves them.
Base change preserves each overlap. Every pair of arrows with equal composites
into Y_j' factors through the base-changed overlap, so restricting its equality
proves Presieve.Arrows.Compatible. The isomorphism d merely changes the target
of the family and cancels in the equal-composite condition. If n = 0, the
compatibility condition is vacuous and the identity refinement suffices. Empty
overlaps cause no exception: a sheaf has a unique section on the empty object.
No section is selected to define an object. -/
theorem etaleSet_eventualLocalStageCompatibility
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
    ∀ (j : Over (op i₀)) (n : ℕ) (V : Fin n → (D.obj j.left).Etale)
      (a : ∀ q, V q ⟶ Y j) (s : ∀ q, (H j).obj.obj (op (V q))),
      (∀ q, IsAffine (V q).left) →
      (∀ q, (β j).hom.app (op (V q)) (s q) =
        L.obj.map ((B j).map (a q) ≫ (e j).inv).op t) →
    ∃ (j' : Over (op i₀)) (r : j' ⟶ j),
      let b := MorphismProperty.Over.pullback @Etale ⊤ (D.map r.left)
      let hr := (D.map_comp r.left j.hom).symm.trans
        (congrArg (fun z : j'.left ⟶ op i₀ ↦ D.map z) r.w)
      let d := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
        (D.map r.left) (D.map j.hom) (D.map j'.hom) hr.symm).app W.obj
      let V' := fun q ↦ b.obj (V q)
      let a' := fun q ↦ b.map (a q) ≫ d.inv
      let s' := fun q ↦ (etaleSetSheafComparison (D.map r.left) (D.map j.hom)
        (D.map j'.hom) hr G).hom.app (op (V q)) (s q)
      Presieve.Arrows.Compatible (H j').obj a' s' := by
  classical
  dsimp only
  intro j n V a s hV hs
  -- On each overlap the limit equation is equality of two comparison images.
  let H := fun k : Over (op i₀) ↦ (Scheme.etaleSetPullback (D.map k.hom)).obj G
  let L := (Scheme.etaleSetPullback (c.π.app (op i₀))).obj G
  let B := MorphismProperty.Over.pullback @Etale ⊤ (c.π.app j.left)
  let Y := (MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj W.obj
  let e := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
    (c.π.app j.left) (D.map j.hom) (c.π.app (op i₀)) (c.w j.hom).symm).app W.obj
  let β := etaleSetSheafComparison (c.π.app j.left) (D.map j.hom)
    (c.π.app (op i₀)) (c.w j.hom) G
  have : IsAffine W.obj.left := W.property
  have hY : IsAffine Y.left := by
    exact @isAffine_of_isAffineHom _ W.obj.left
      (pullback.fst W.obj.hom (D.map j.hom))
      (MorphismProperty.pullback_fst _ _ (inferInstance : IsAffineHom (D.map j.hom)))
      W.property
  have : QuasiCompact Y.hom := @quasiCompact_of_compactSpace _ _ Y.hom
    (@Scheme.compactSpace_of_isAffine _ hY) (inferInstance : QuasiSeparatedSpace (D.obj j.left))
  have : QuasiSeparated Y.hom := @QuasiSeparated.of_quasiSeparatedSpace _ _ Y.hom
    (@quasiSeparatedSpace_of_isAffine _ hY)
  have hpair (x : Fin n × Fin n) :
      ∃ (l : Over (op i₀)) (d : l ⟶ j),
        ∀ (k : Over (op i₀)) (v : k ⟶ l) (T : (D.obj k.left).Etale)
          (p : T ⟶ (MorphismProperty.Over.pullback @Etale ⊤
            (D.map (v ≫ d).left)).obj (V x.1))
          (q : T ⟶ (MorphismProperty.Over.pullback @Etale ⊤
            (D.map (v ≫ d).left)).obj (V x.2)),
          p ≫ (MorphismProperty.Over.pullback @Etale ⊤
            (D.map (v ≫ d).left)).map (a x.1) =
            q ≫ (MorphismProperty.Over.pullback @Etale ⊤
              (D.map (v ≫ d).left)).map (a x.2) →
          (H k).obj.map p.op
            ((etaleSetSheafComparison (D.map (v ≫ d).left) (D.map j.hom)
              (D.map k.hom) ((D.map_comp (v ≫ d).left j.hom).symm.trans
                (congrArg (fun z : k.left ⟶ op i₀ ↦ D.map z) (v ≫ d).w)) G).hom.app
                  (op (V x.1)) (s x.1)) =
          (H k).obj.map q.op
            ((etaleSetSheafComparison (D.map (v ≫ d).left) (D.map j.hom)
              (D.map k.hom) ((D.map_comp (v ≫ d).left j.hom).symm.trans
                (congrArg (fun z : k.left ⟶ op i₀ ↦ D.map z) (v ≫ d).w)) G).hom.app
                  (op (V x.2)) (s x.2)) := by
    have : IsAffine (V x.1).left := hV x.1
    have : IsAffine (V x.2).left := hV x.2
    have : QuasiCompact (V x.1).hom := @quasiCompact_of_compactSpace _ _ (V x.1).hom
      (@Scheme.compactSpace_of_isAffine _ (hV x.1))
      (inferInstance : QuasiSeparatedSpace (D.obj j.left))
    have : QuasiCompact (V x.2).hom := @quasiCompact_of_compactSpace _ _ (V x.2).hom
      (@Scheme.compactSpace_of_isAffine _ (hV x.2))
      (inferInstance : QuasiSeparatedSpace (D.obj j.left))
    have : QuasiSeparated (V x.1).hom := @QuasiSeparated.of_quasiSeparatedSpace _ _ (V x.1).hom
      (@quasiSeparatedSpace_of_isAffine _ (hV x.1))
    have : QuasiSeparated (V x.2).hom := @QuasiSeparated.of_quasiSeparatedSpace _ _ (V x.2).hom
      (@quasiSeparatedSpace_of_isAffine _ (hV x.2))
    obtain ⟨Z, p, q, hqc, hqs, hpq, hdetect⟩ :=
      etale_pair_restriction_detection Y (V x.1) (V x.2) (a x.1) (a x.2)
    have : QuasiCompact Z.hom := hqc
    have hmatch : β.hom.app (op Z) ((H j).obj.map p.op (s x.1)) =
        β.hom.app (op Z) ((H j).obj.map q.op (s x.2)) := by
      have hn₁ := ConcreteCategory.congr_hom (β.hom.naturality p.op) (s x.1)
      have hn₂ := ConcreteCategory.congr_hom (β.hom.naturality q.op) (s x.2)
      change β.hom.app (op Z) ((H j).obj.map p.op (s x.1)) =
        L.obj.map (B.map p).op (β.hom.app (op (V x.1)) (s x.1)) at hn₁
      change β.hom.app (op Z) ((H j).obj.map q.op (s x.2)) =
        L.obj.map (B.map q).op (β.hom.app (op (V x.2)) (s x.2)) at hn₂
      rw [hn₁, hn₂, hs x.1, hs x.2]
      change L.obj.map (B.map p).op (L.obj.map (B.map (a x.1) ≫ e.inv).op t) =
        L.obj.map (B.map q).op (L.obj.map (B.map (a x.2) ≫ e.inv).op t)
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
      congr 2
      rw [← Category.assoc, ← Category.assoc, ← B.map_comp, ← B.map_comp, hpq]
    obtain ⟨l, d, heq⟩ := comparison_eventually_equal D c hc i₀ G j Z
      ((H j).obj.map p.op (s x.1)) ((H j).obj.map q.op (s x.2)) hmatch
    refine ⟨l, d, ?_⟩
    intro k v T p' q' hp'q'
    let γ := etaleSetSheafComparison (D.map (v ≫ d).left) (D.map j.hom)
      (D.map k.hom) ((D.map_comp (v ≫ d).left j.hom).symm.trans
        (congrArg (fun z : k.left ⟶ op i₀ ↦ D.map z) (v ≫ d).w)) G
    apply hdetect (D.obj k.left) (D.map (v ≫ d).left) (H k)
      (γ.hom.app (op (V x.1)) (s x.1)) (γ.hom.app (op (V x.2)) (s x.2)) ?_
      T p' q' hp'q'
    have hn₁ := ConcreteCategory.congr_hom (γ.hom.naturality p.op) (s x.1)
    have hn₂ := ConcreteCategory.congr_hom (γ.hom.naturality q.op) (s x.2)
    exact hn₁.symm.trans ((heq k v).trans hn₂)
  -- Combine all pairwise witnesses at one common later stage, also when n = 0.
  choose M A hmatch using hpair
  obtain ⟨l, hl⟩ := IsCofiltered.inf_objs_exists (insert j (Finset.univ.image M))
  let r : l ⟶ j := (hl (Finset.mem_insert_self _ _)).some
  let v (x : Fin n × Fin n) : l ⟶ M x := (hl (Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩))).some
  refine ⟨l, r, ?_⟩
  intro q q' T p p' hp
  have hv : v (q, q') ≫ A (q, q') = r := by
    apply Over.OverMorphism.ext
    exact Subsingleton.elim _ _
  have hp' : p ≫ (MorphismProperty.Over.pullback @Etale ⊤ (D.map r.left)).map (a q) =
      p' ≫ (MorphismProperty.Over.pullback @Etale ⊤ (D.map r.left)).map (a q') := by
    apply (cancel_mono
      ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
        (D.map r.left) (D.map j.hom) (D.map l.hom)
        ((D.map_comp r.left j.hom).symm.trans
          (congrArg (fun z : l.left ⟶ op i₀ ↦ D.map z) r.w)).symm).app W.obj).inv).mp
    simpa only [Category.assoc] using hp
  have heq := hmatch (q, q') l (v (q, q'))
  rw [hv] at heq
  exact heq T p p' hp'

end AlgebraicGeometry
