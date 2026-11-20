import Langlands.GroupScheme.HomScheme.AdicSplitTorusGraphImage

/-! # Descent from a finite schematic graph image -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.HomScheme

open Diagonalizable TorsionDensity

variable {R B : Type u} [CommRing R] [CommRing B]
variable (L : Type u) [Fintype L] (φ : R →+* B)
variable {G : GroupScheme (Spec (CommRingCat.of R))} [IsSeparated G.X.hom]

local notation "b" => Spec.map (CommRingCat.ofHom φ)
local notation "H" => CommGroupScheme.toGrp (groupScheme (CommRingCat.of R) (L → ℤ))
local notation "D" n =>
  CommGroupScheme.toGrp (groupScheme (CommRingCat.of R) ((L → ℤ) ⧸ multiples (L → ℤ) n))

/-- Split-torus homomorphisms with finite schematic graph image descend along
injective scalar extensions if their positive torsion restrictions descend. -/
def FiniteSplitTorusGraphDescentStatement : Prop :=
  ∀ (R B : Type u) [CommRing R] [CommRing B]
    (L : Type u) [Fintype L] (φ : R →+* B), Function.Injective φ →
  ∀ (G : GroupScheme (Spec (CommRingCat.of R))) [IsSeparated G.X.hom],
    let source := (groupScheme (CommRingCat.of R) (L → ℤ)).toGrp
    let projection := Spec.map (CommRingCat.ofHom φ)
    ∀ (f : RelativeHom source G (Over.mk projection)),
      IsFinite ((relativeGraphMap f).imageι ≫ (fst source G).hom.hom.left) →
      (∀ n : ℕ, 0 < n →
        ∃ g : (groupScheme (CommRingCat.of R) ((L → ℤ) ⧸ multiples (L → ℤ) n)).toGrp ⟶ G,
          (baseChange projection).map g =
            (baseChange projection).map (splitTorsionRestriction (CommRingCat.of R) L n) ≫ f) →
      ∃! g : source ⟶ G, (baseChange projection).map g = f

set_option maxHeartbeats 1000000 in
/-- Lift the torsion graphs into the finite affine image, descend its coordinates,
and recover the group law by schematic dominance. -/
theorem existsUnique_hom_of_finite_graph_image
    (hφ : Function.Injective φ)
    (f : RelativeHom (H) G (Over.mk b))
    (hfin : IsFinite ((relativeGraphMap f).imageι ≫ (fst (H) G).hom.hom.left))
    (ht : ∀ n : ℕ, 0 < n → ∃ g : (D n) ⟶ G,
      (baseChange b).map g =
        (baseChange b).map (splitTorsionRestriction (CommRingCat.of R) L n) ≫ f) :
    ∃! g : H ⟶ G, (baseChange b).map g = f := by
  let a := relativeGraphMap f
  let e := baseChangeIso b (L → ℤ)
  let p := pullback.fst (H).X.hom b
  let : IsAffine (H).X.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (AddMonoidAlgebra R (L → ℤ)))))
  let : IsFinite (a.imageι ≫ (fst (H) G).hom.hom.left) := hfin
  let : IsAffine a.image := isAffine_of_isAffineHom (a.imageι ≫ (fst (H) G).hom.hom.left)
  let : IsSchemeTheoreticallyDominant b := isSchemeTheoreticallyDominant_specMap hφ
  have htor (n : ℕ) (hn : 0 < n) :
      ∃ g : (D n).X.left ⟶ a.image,
        coefficientProjection _ φ ≫ g = torsionProjection L B n ≫ e.inv.hom.hom.left ≫ a.toImage := by
    obtain ⟨g, hg⟩ := ht n hn
    let j := splitTorsionRestriction (CommRingCat.of R) L n
    let jB := splitTorsionRestriction (CommRingCat.of B) L n
    let j' := (baseChange b).map j
    let pD : ((baseChange b).obj (D n)).X.left ⟶ (D n).X.left :=
      pullback.fst (D n).X.hom b
    let d := baseChangeIso b ((L → ℤ) ⧸ multiples (L → ℤ) n)
    have hd : d.inv ≫ j' = jB ≫ e.inv := by
      apply (cancel_mono e.hom).mp
      rw [Category.assoc, baseChangeIso_restrictMap, Iso.inv_hom_id_assoc,
        Category.assoc, Iso.inv_hom_id, Category.comp_id]
    let k : (D n).X.left ⟶ (H ⊗ G).X.left :=
      pullback.lift j.hom.hom.left g.hom.hom.left
        ((Over.w j.hom.hom).trans (Over.w g.hom.hom).symm)
    have hk : pD ≫ k = j'.hom.hom.left ≫ a := by
      apply pullback.hom_ext
      · let proj := (fst (H) G).hom.hom.left
        change (pD ≫ k) ≫ proj = (j'.hom.hom.left ≫ a) ≫ proj
        have h₁ : k ≫ proj = j.hom.hom.left := pullback.lift_fst _ _ _
        have h₂ : a ≫ proj = pullback.fst (H).X.hom b := relativeGraphMap_fst f
        simpa only [Category.assoc, h₁, h₂] using (baseChange_map_left_fst b j).symm
      · let proj := (snd (H) G).hom.hom.left
        change (pD ≫ k) ≫ proj = (j'.hom.hom.left ≫ a) ≫ proj
        have h₁ : k ≫ proj = g.hom.hom.left := pullback.lift_snd _ _ _
        have h₂ : a ≫ proj = f.hom.hom.left ≫ pullback.fst G.X.hom b :=
          relativeGraphMap_snd f
        have h₃ := congrArg (fun z => z.hom.hom.left ≫ pullback.fst G.X.hom b) hg
        simpa only [Category.assoc, h₁, h₂, Grp.comp_hom_hom, Over.comp_left,
          baseChange_map_left_fst] using h₃
    let : IsSchemeTheoreticallyDominant pD := by
      change IsSchemeTheoreticallyDominant (pullback.fst (D n).X.hom b)
      infer_instance
    have hker : a.imageι.ker ≤ k.ker := by
      have h := Scheme.Hom.le_ker_comp (j'.hom.hom.left ≫ a.toImage) a.imageι
      rwa [Category.assoc, Scheme.Hom.toImage_imageι, ← hk, Scheme.Hom.ker_comp,
        pD.ker_eq_bot, Scheme.IdealSheafData.map_bot] at h
    let l := IsClosedImmersion.lift a.imageι k hker
    have hl : pD ≫ l = j'.hom.hom.left ≫ a.toImage := by
      apply (cancel_mono a.imageι).mp
      have hlift : l ≫ a.imageι = k := IsClosedImmersion.lift_fac _ _ _
      simpa only [Category.assoc, hlift, Scheme.Hom.toImage_imageι] using hk
    refine ⟨l, ?_⟩
    have he := congrArg (fun z => d.inv.hom.hom.left ≫ z) hl
    rw [← Category.assoc, baseChangeIso_inv_fst, ← Category.assoc, ← Over.comp_left,
      ← Grp.comp_hom_hom, hd, Grp.comp_hom_hom, Over.comp_left, Category.assoc] at he
    have hjB : jB.hom.hom.left = torsionProjection L B n := restrictMap_left _ _
    simpa only [hjB] using he
  obtain ⟨g, hg, _⟩ := existsUnique_hom_of_torsion_coefficients L φ hφ
    (e.inv.hom.hom.left ≫ a.toImage) (0 < ·)
    (fun n => ⟨n + 1, Nat.zero_lt_succ n, Nat.lt_succ_self n⟩) htor
  have hg₀ : p ≫ g = a.toImage := by
    apply (cancel_epi e.inv.hom.hom.left).mp
    rwa [← Category.assoc, baseChangeIso_inv_fst]
  let g₀ := g ≫ a.imageι ≫ (snd (H) G).hom.hom.left
  have hg₁ : p ≫ g₀ = f.hom.hom.left ≫ pullback.fst G.X.hom b := by
    rw [← Category.assoc, ← Category.assoc, hg₀, Scheme.Hom.toImage_imageι, relativeGraphMap_snd]
    rfl
  let g' : (H).X ⟶ G.X := Over.homMk g₀ (by
    let : IsSchemeTheoreticallyDominant p := by
      change IsSchemeTheoreticallyDominant (pullback.fst (H).X.hom b)
      infer_instance
    apply ext_of_isSchemeTheoreticallyDominant (terminal.from (Spec (CommRingCat.of R)))
      (terminal.hom_ext _ _) p
    have hw : f.hom.hom.left ≫ pullback.snd G.X.hom b = pullback.snd (H).X.hom b := Over.w f.hom.hom
    rw [← Category.assoc, hg₁, Category.assoc, pullback.condition, ← Category.assoc, hw]
    exact pullback.condition.symm)
  apply existsUnique_hom_of_pullback_schemeMap b f g'
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (pullback.lift_fst _ _ _).trans hg₁
  · exact (Over.w ((Over.pullback b).map g')).trans (Over.w f.hom.hom).symm

/-- Finite schematic graph descent for split-torus homomorphisms. -/
theorem finiteSplitTorusGraphDescent : FiniteSplitTorusGraphDescentStatement.{u} := by
  intro R B _ _ L _ φ hφ G _ source projection f hfin ht
  exact existsUnique_hom_of_finite_graph_image L φ hφ f hfin ht

end Langlands.GroupScheme.HomScheme
