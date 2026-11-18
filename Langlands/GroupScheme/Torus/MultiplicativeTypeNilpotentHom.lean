import Langlands.GroupScheme.Torus.DiagonalizableTopologicalHom
import Langlands.GroupScheme.Torus.MultiplicativeTypePointwiseSplitting
import Langlands.GroupScheme.Descent.EtaleCoverHomDescent
import Langlands.GroupScheme.Descent.SemilinearDatum
import Mathlib.CategoryTheory.HomCongr
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Homomorphisms of multiplicative-type groups across a thickening -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.RelativeMultiplicativeType

open Descent

variable {S S₀ T U : Scheme.{u}} {G H : GroupScheme S}

/-- Base change along a homeomorphism of underlying spaces is bijective on
homomorphisms between diagonalizable group schemes. -/
theorem IsDiagonalizable.baseChange_hom_bijective_of_isHomeomorph
    (hG : IsDiagonalizable G) (hH : IsDiagonalizable H)
    (r : S₀ ⟶ S) (hr : IsHomeomorph r) :
    Function.Bijective (fun a : G ⟶ H => (GroupScheme.baseChange r).map a) := by
  obtain ⟨M, _, _, ⟨eG⟩⟩ := hG
  obtain ⟨N, _, _, ⟨eH⟩⟩ := hH
  let e := eG.homCongr eH
  let e₀ := ((GroupScheme.baseChange r).mapIso eG ≪≫ diagonalizableBaseChangeIso r M).homCongr
    ((GroupScheme.baseChange r).mapIso eH ≪≫ diagonalizableBaseChangeIso r N)
  have hc (a : G ⟶ H) : e₀ ((GroupScheme.baseChange r).map a) = dpull r (e a) := by
    simp [e, e₀, dpull_eq, Functor.map_comp]
  have hd := dpull_bijective_of_isHomeomorph (M := M) (N := N) r hr
  constructor
  · intro a b hab
    apply e.injective
    apply hd.injective
    rw [← hc, ← hc]
    exact congrArg e₀ hab
  · intro a₀
    obtain ⟨b, hb⟩ := hd.surjective (e₀ a₀)
    refine ⟨e.symm b, e₀.injective ?_⟩
    rw [hc, Equiv.apply_symm_apply, hb]

/-- Pullback through a surjective closed immersion is bijective on
diagonalizable Hom sets, with either endpoint expressed as a direct pullback. -/
theorem pullHom_bijective_of_diagonalizable (q : U ⟶ T)
    [IsClosedImmersion q] [Surjective q] {f g : T ⟶ S} {a b : U ⟶ S}
    (ha : q ≫ f = a) (hb : q ≫ g = b)
    (hG : IsDiagonalizable ((GroupScheme.baseChange f).obj G))
    (hH : IsDiagonalizable ((GroupScheme.baseChange g).obj H)) :
    Function.Bijective (pullHom q ha hb (G := G) (H := H)) :=
  ((pullbackComparison f q a ha G).homCongr
    (pullbackComparison g q b hb H)).bijective.comp
    (hG.baseChange_hom_bijective_of_isHomeomorph hH q
      (isHomeomorph_iff_isEmbedding_surjective.mpr
        ⟨q.isClosedEmbedding.isEmbedding, q.surjective⟩))

/-- A common étale splitting cover for two groups of multiplicative type. -/
def commonEtaleSplittingCover (hG : IsMultiplicativeType G) (hH : IsMultiplicativeType H) :
    {𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S //
      ∀ i, IsDiagonalizable ((GroupScheme.baseChange (𝒰.f i)).obj G) ∧
        IsDiagonalizable ((GroupScheme.baseChange (𝒰.f i)).obj H)} := by
  classical
  have h (s : S) : ∃ (V : Scheme.{u}) (p : V ⟶ S), Etale p ∧ s ∈ Set.range p ∧
      IsDiagonalizable ((GroupScheme.baseChange p).obj G) ∧ IsDiagonalizable ((GroupScheme.baseChange p).obj H) := by
    obtain ⟨V, p, hp, ⟨v, hv⟩, hdG⟩ := hG.exists_etale_diagonalizable s
    obtain ⟨W, q, hq, ⟨w, hw⟩, hdH⟩ := (hH.baseChange p).exists_etale_diagonalizable v
    let _ : Etale p := hp
    let _ : Etale q := hq
    refine ⟨W, q ≫ p, inferInstance, ⟨w, ?_⟩, ?_, ?_⟩
    · change p (q w) = s
      rw [hw, hv]
    · exact (hdG.baseChange q).of_iso (baseChangeCompIso p q G)
    · exact hdH.of_iso (baseChangeCompIso p q H)
  choose V p hp hs hG' hH' using h
  refine ⟨Scheme.Cover.mkOfCovers S V p (fun s => ?_) hp, fun i => ⟨hG' i, hH' i⟩⟩
  obtain ⟨v, hv⟩ := hs s
  exact ⟨s, v, hv⟩

/-- Reduce a map over a chart, with both endpoints pulled back from the
original base along the common composite. -/
abbrev reduceHom (r : S₀ ⟶ S) (p : T ⟶ S)
    (a : (GroupScheme.baseChange p).obj G ⟶ (GroupScheme.baseChange p).obj H) :
    (GroupScheme.baseChange (pullback.fst r p ≫ r)).obj G ⟶
      (GroupScheme.baseChange (pullback.fst r p ≫ r)).obj H :=
  pullHom (pullback.snd r p) pullback.condition.symm pullback.condition.symm a

private theorem reduceHom_bijective (r : S₀ ⟶ S) [IsClosedImmersion r] [Surjective r]
    (p : T ⟶ S) (hG : IsDiagonalizable ((GroupScheme.baseChange p).obj G))
    (hH : IsDiagonalizable ((GroupScheme.baseChange p).obj H)) :
    Function.Bijective (reduceHom r p (G := G) (H := H)) :=
  pullHom_bijective_of_diagonalizable (pullback.snd r p)
    pullback.condition.symm pullback.condition.symm hG hH

private theorem reduceHom_restrict (r : S₀ ⟶ S) (p : T ⟶ S)
    (q : U ⟶ T) (t : U ⟶ S) (h : q ≫ p = t)
    (a : (GroupScheme.baseChange p).obj G ⟶ (GroupScheme.baseChange p).obj H)
    (a₀ : (GroupScheme.baseChange r).obj G ⟶ (GroupScheme.baseChange r).obj H)
    (ha : reduceHom r p a = pullHom (pullback.fst r p) rfl rfl a₀) :
    reduceHom r t (pullHom q h h a) = pullHom (pullback.fst r t) rfl rfl a₀ := by
  let d : pullback r t ⟶ pullback r p :=
    pullback.lift (pullback.fst r t) (pullback.snd r t ≫ q) (by
      rw [Category.assoc, h, pullback.condition])
  have hf : d ≫ pullback.fst r p = pullback.fst r t := pullback.lift_fst _ _ _
  have hg : d ≫ pullback.snd r p = pullback.snd r t ≫ q := pullback.lift_snd _ _ _
  have hd : d ≫ (pullback.fst r p ≫ r) = pullback.fst r t ≫ r := by
    rw [← Category.assoc, hf]
  calc
    reduceHom r t (pullHom q h h a) =
        pullHom d hd hd (reduceHom r p a) := by
      simp only [reduceHom, pullHom_pullHom]
      exact pullHom_congr_map hg.symm _ _ a
    _ = pullHom (pullback.fst r t) rfl rfl a₀ := by
      rw [ha, pullHom_pullHom]
      exact pullHom_congr_map hf _ _ a₀

private theorem compatible_of_overlap {𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S}
    (a : ∀ i, (GroupScheme.baseChange (𝒰.f i)).obj G ⟶ (GroupScheme.baseChange (𝒰.f i)).obj H)
    (ha : ∀ i j, pullHom (pullback.fst (𝒰.f i) (𝒰.f j)) rfl rfl (a i) =
      pullHom (pullback.snd (𝒰.f i) (𝒰.f j)) pullback.condition.symm
        pullback.condition.symm (a j)) :
    EtaleCoverHomDescent.Compatible 𝒰 a := by
  intro Z i j x y hxy
  let f := 𝒰.f i
  let g := 𝒰.f j
  let z : Z ⟶ pullback f g :=
    pullback.lift (x ≫ pullback.snd G.X.hom f) (y ≫ pullback.snd G.X.hom g) (by
      simp only [Category.assoc, ← pullback.condition]
      rw [← Category.assoc, ← Category.assoc, hxy])
  have hz₁ : z ≫ pullback.fst f g = x ≫ pullback.snd G.X.hom f :=
    pullback.lift_fst _ _ _
  have hz₂ : z ≫ pullback.snd f g = y ≫ pullback.snd G.X.hom g :=
    pullback.lift_snd _ _ _
  let w := x ≫ pullback.fst G.X.hom f
  have hw : w ≫ G.X.hom = z ≫ (pullback.fst f g ≫ f) := by
    calc
      w ≫ G.X.hom = x ≫ pullback.fst G.X.hom f ≫ G.X.hom := Category.assoc _ _ _
      _ = x ≫ pullback.snd G.X.hom f ≫ f := by rw [pullback.condition]
      _ = (x ≫ pullback.snd G.X.hom f) ≫ f := (Category.assoc _ _ _).symm
      _ = (z ≫ pullback.fst f g) ≫ f := congrArg (fun k => k ≫ f) hz₁.symm
      _ = z ≫ (pullback.fst f g ≫ f) := Category.assoc _ _ _
  have hx {hx' : w ≫ G.X.hom = (z ≫ pullback.fst f g) ≫ f} :
      pullback.lift w (z ≫ pullback.fst f g) hx' = x := by
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · rw [pullback.lift_snd, hz₁]
  have hy {hy' : w ≫ G.X.hom = (z ≫ pullback.snd f g) ≫ g} :
      pullback.lift w (z ≫ pullback.snd f g) hy' = y := by
    apply pullback.hom_ext
    · simpa only [pullback.lift_fst, w] using hxy
    · rw [pullback.lift_snd, hz₂]
  have hi := pullHom_eval (pullback.fst f g) rfl rfl (a i) w z hw
  have hj := pullHom_eval (pullback.snd f g) pullback.condition.symm
    pullback.condition.symm (a j) w z hw
  rw [hx] at hi
  rw [hy] at hj
  calc
    _ = pullback.lift w z hw ≫ (pullHom (pullback.fst f g) rfl rfl (a i)).hom.hom.left ≫
        pullback.fst H.X.hom (pullback.fst f g ≫ f) := hi.symm
    _ = pullback.lift w z hw ≫ (pullHom (pullback.snd f g) pullback.condition.symm
        pullback.condition.symm (a j)).hom.hom.left ≫
        pullback.fst H.X.hom (pullback.fst f g ≫ f) := by
      exact congrArg
        (fun b : (GroupScheme.baseChange (pullback.fst f g ≫ f)).obj G ⟶
          (GroupScheme.baseChange (pullback.fst f g ≫ f)).obj H =>
          pullback.lift w z hw ≫ b.hom.hom.left ≫ pullback.fst H.X.hom
            (pullback.fst f g ≫ f)) (ha i j)
    _ = _ := hj

/-- Reduction along a surjective closed immersion is fully faithful on the
actual Hom sets of groups of multiplicative type. -/
theorem IsMultiplicativeType.baseChange_hom_bijective_of_surjective_closedImmersion
    (hG : IsMultiplicativeType G) (hH : IsMultiplicativeType H)
    (r : S₀ ⟶ S) [IsClosedImmersion r] [Surjective r] :
    Function.Bijective (fun a : G ⟶ H => (GroupScheme.baseChange r).map a) := by
  classical
  obtain ⟨𝒰, h𝒰⟩ := commonEtaleSplittingCover hG hH
  constructor
  · intro a b hab
    apply EtaleCoverHomDescent.groupHom_ext 𝒰
    intro i
    apply (reduceHom_bijective r (𝒰.f i) (h𝒰 i).1 (h𝒰 i).2).injective
    simpa only [reduceHom, pullHom_map] using
      congrArg (pullHom (pullback.fst r (𝒰.f i)) rfl rfl) hab
  · intro a₀
    choose a ha using fun i =>
      (reduceHom_bijective r (𝒰.f i) (h𝒰 i).1 (h𝒰 i).2).surjective
        (pullHom (pullback.fst r (𝒰.f i)) rfl rfl a₀)
    have ha' : EtaleCoverHomDescent.Compatible 𝒰 a := by
      apply compatible_of_overlap
      intro i j
      let p := 𝒰.f i
      let q := 𝒰.f j
      let t := pullback.fst p q ≫ p
      have hD {K : GroupScheme S} (hK : IsDiagonalizable ((GroupScheme.baseChange p).obj K)) :
          IsDiagonalizable ((GroupScheme.baseChange t).obj K) :=
        (hK.baseChange (pullback.fst p q)).of_iso (baseChangeCompIso p (pullback.fst p q) K)
      apply (reduceHom_bijective r t (hD (h𝒰 i).1) (hD (h𝒰 i).2)).injective
      exact (reduceHom_restrict r p (pullback.fst p q) t rfl (a i) a₀ (ha i)).trans
        (reduceHom_restrict r q (pullback.snd p q) t pullback.condition.symm
          (a j) a₀ (ha j)).symm
    let b := EtaleCoverHomDescent.hom 𝒰 a ha'
    refine ⟨b, ?_⟩
    apply EtaleCoverHomDescent.groupHom_ext (𝒰.pullback₁ r)
    intro i
    let v := pullback.fst r (𝒰.f i)
    apply (Iso.homCongr (pullbackComparison r v (v ≫ r) rfl G)
      (pullbackComparison r v (v ≫ r) rfl H)).injective
    change pullHom v rfl rfl ((GroupScheme.baseChange r).map b) = pullHom v rfl rfl a₀
    rw [pullHom_map, ← ha i]
    calc
      _ = reduceHom r (𝒰.f i) ((GroupScheme.baseChange (𝒰.f i)).map b) :=
        (pullHom_map (pullback.snd r (𝒰.f i)) (𝒰.f i) (v ≫ r)
          pullback.condition.symm b).symm
      _ = _ := congrArg (reduceHom r (𝒰.f i)) (EtaleCoverHomDescent.baseChange_hom 𝒰 a ha' i)

end Langlands.GroupScheme.RelativeMultiplicativeType
