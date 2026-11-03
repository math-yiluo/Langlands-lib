import Langlands.GroupScheme.Dynamic.SchemeActionLimit
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.HomConjugacy
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.QuotientCell
import Langlands.GroupScheme.Dynamic.OppositeCellContraction
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Absolute.OppositeCellProof
import Langlands.GroupScheme.Torus.Maximal

/-! # A double coset from the limit of a cocharacter orbit in a subgroup quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic.BruhatCellLimit

section Cell

variable {k : Type u} [Field k] {G P U : GroupScheme (Spec (CommRingCat.of k))}
  (iP : P ⟶ G) (iU : U ⟶ G) {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
  (a : SchemeAction G Q)
  (hact : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
    a.act g (h ≫ q) = (g * h) ≫ q)
  (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
    g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range iP).carrier T)

include hact hfib in
/-- The cell `U ⟶ Q`, `u ↦ u·x₀`, is stable under a cocharacter `ψ` whose range lies in `P`
and normalizes `U`. -/
theorem isGmStable_cell (ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hψP : SubgroupFunctor.range ψ ≤ SubgroupFunctor.range iP)
    (hψU : (SubgroupFunctor.range iU).IsNormalizedBy (SubgroupFunctor.range ψ)) :
    (a.restrict ψ).IsGmStable (iU.hom.hom ≫ q) := by
  intro T s z
  have hm : s ≫ ψ.hom.hom ∈ (SubgroupFunctor.range ψ).carrier T :=
    SubgroupFunctor.mem_range.mpr ⟨s, rfl⟩
  obtain ⟨z', hz'⟩ := SubgroupFunctor.mem_range.mp
    (hψU T _ _ hm (SubgroupFunctor.mem_range.mpr ⟨z, rfl⟩))
  refine ⟨z', ?_⟩
  rw [SchemeAction.restrict_act, ← Category.assoc z, hact, ← Category.assoc, hz']
  apply (hfib T _ _).mpr
  have hP := hψP T hm
  convert hP using 1
  group

include hact hfib in
/-- **The cell argument.** Let `x = g·x₀` and let `e` extend the `χ`-orbit of `x` to the
affine line. Suppose its limit is `n·x₀`, and `ψ = n⁻¹χn` has range in `P` and normalizes `U`.
If `U × P ⟶ G` is an open immersion and `P(χ) ≤ P`, then `g ∈ P n P`. -/
theorem exists_eq_mul_mul [IsSeparated Q.hom] [Mono iP.hom.hom]
    [Surjective q.left] [Flat q.left] [QuasiCompact q.left]
    (hcell : IsOpenImmersion
      ((fst U.X P.X ≫ iU.hom.hom) * (snd U.X P.X ≫ iP.hom.hom)).left)
    (χ ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (n g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hψ : ψ ≫ (G.innerIso n).hom = χ)
    (hχP : parabolic χ ≤ SubgroupFunctor.range iP)
    (hψP : SubgroupFunctor.range ψ ≤ SubgroupFunctor.range iP)
    (hψU : (SubgroupFunctor.range iU).IsNormalizedBy (SubgroupFunctor.range ψ))
    {e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗
      AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ Q}
    (he : (a.restrict χ).IsGmOrbitExtension (g ≫ q) e)
    (hn : evalZero e = n ≫ q) :
    ∃ b₁ b₂ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X,
      g = (b₁ ≫ iP.hom.hom) * n * (b₂ ≫ iP.hom.hom) := by
  have hχ : ∀ (T : Over (Spec (CommRingCat.of k)))
      (s : T ⟶ (Gm (Spec (CommRingCat.of k))).X),
      s ≫ χ.hom.hom =
        G.constantPoint n T * (s ≫ ψ.hom.hom) * (G.constantPoint n T)⁻¹ := by
    intro T s
    rw [← comp_innerIso_hom, ← hψ, Grp.comp_hom_hom, Category.assoc]
  have hbase : ∀ {T : Over (Spec (CommRingCat.of k))}
      (c : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k)))), c ≫ n = G.constantPoint n T :=
    fun c => by rw [← G.constantPoint_naturality n c, constantPoint_self]
  -- Translate the extension by `n⁻¹`: it extends the `ψ`-orbit of `n⁻¹g·x₀`.
  set e' := a.act (G.constantPoint n⁻¹ _) e with he'_def
  have he' : (a.restrict ψ).IsGmOrbitExtension ((n⁻¹ * g) ≫ q) e' := by
    rw [SchemeAction.IsGmOrbitExtension, he'_def, a.naturality, G.constantPoint_naturality, he,
      SchemeAction.gmOrbit, SchemeAction.gmOrbit, SchemeAction.restrict_act,
      SchemeAction.restrict_act, ← Category.assoc (fst _ _) g q,
      ← Category.assoc (fst _ _) (n⁻¹ * g) q]
    simp only [hact]
    congr 1
    rw [hχ, MonObj.comp_mul, GrpObj.comp_inv, hbase, constantPoint_inv]
    group
  have : IsOpenImmersion (QuotientCell.multiplication iP iU.hom.hom).left := hcell
  have : IsOpenImmersion (iU.hom.hom ≫ q).left :=
    QuotientCell.isOpenImmersion iP iU.hom.hom q hfib
  have h0eq : evalZero e' = (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X) ≫
      iU.hom.hom ≫ q := by
    have hn' := hn
    unfold evalZero at hn' ⊢
    rw [he'_def, a.naturality, G.constantPoint_naturality, hn', hact, constantPoint_self,
      inv_mul_cancel, ← Category.assoc (1 : _ ⟶ U.X), MonObj.one_comp iU.hom.hom]
  have h0 : (evalZero e').left (⊥ : PrimeSpectrum k) ∈ (iU.hom.hom ≫ q).left.opensRange := by
    rw [h0eq]
    exact ⟨_, rfl⟩
  -- The translated extension lands in the open cell `U·x₀`.
  have hst := isGmStable_cell iP iU q a hact hfib ψ hψP hψU
  set f := SchemeAction.gmOrbitOpenLift (a.restrict ψ) (iU.hom.hom ≫ q) hst he' h0 with hf_def
  have hf : f ≫ iU.hom.hom ≫ q = e' := SchemeAction.gmOrbitOpenLift_fac _ _ _ _ _
  -- Its value at `1` is a point `u` of `U` with `u·x₀ = n⁻¹g·x₀`.
  set u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X :=
    lift (𝟙 _) (toUnit _ ≫ η[(Gm (Spec (CommRingCat.of k))).X]) ≫
      _ ◁ AffineLine.unitInclusion _ ≫ f with hu_def
  have hu : (u ≫ iU.hom.hom) ≫ q = (n⁻¹ * g) ≫ q := by
    rw [hu_def, Category.assoc, Category.assoc, Category.assoc, hf]
    exact he'.eval_one
  obtain ⟨b₂, hb₂⟩ := SubgroupFunctor.mem_range.mp ((hfib _ _ _).mp hu)
  -- The `ψ`-orbit of `u` extends through `f`, so `u ∈ P(ψ)`.
  have hm : snd (Over.mk (𝟙 (Spec (CommRingCat.of k)))) (Gm (Spec (CommRingCat.of k))).X ≫
      ψ.hom.hom ∈ (SubgroupFunctor.range ψ).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗ (Gm (Spec (CommRingCat.of k))).X) :=
    SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩
  obtain ⟨z', hz'⟩ := SubgroupFunctor.mem_range.mp
    (hψU _ _ _ hm (SubgroupFunctor.mem_range.mpr ⟨fst _ _ ≫ u, rfl⟩))
  have hF : _ ◁ AffineLine.unitInclusion _ ≫ f = z' := by
    apply Over.OverMorphism.ext
    apply (cancel_mono (iU.hom.hom ≫ q).left).mp
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [Category.assoc, hf, he', SchemeAction.gmOrbit, SchemeAction.restrict_act, ← hu,
      ← Category.assoc z', hz', ← Category.assoc (fst _ _) (u ≫ iU.hom.hom) q,
      ← Category.assoc (fst _ _) u, hact]
    apply (hfib _ _ _).mpr
    convert (SubgroupFunctor.range iP).carrier _ |>.inv_mem (hψP _ hm) using 1
    group
  have hpar : u ≫ iU.hom.hom ∈ (parabolic ψ).carrier _ := by
    refine ⟨f ≫ iU.hom.hom, ?_⟩
    rw [IsOrbitExtension, ← Category.assoc, hF, hz', orbit, Category.assoc]
  -- Conjugating by `n` puts `n u n⁻¹` in `P(χ) ≤ P`.
  have hconj := (mem_parabolic_conj ψ n).mp hpar
  rw [hψ, constantPoint_self] at hconj
  obtain ⟨b₁, hb₁⟩ := SubgroupFunctor.mem_range.mp (hχP _ hconj)
  refine ⟨b₁, b₂, ?_⟩
  rw [hb₁, hb₂]
  group

end Cell

section BorelPair

variable {k : Type u} [Field k] {G B : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- **The cell argument for a Borel pair.** Let `B = P_G(νj)` for a cocharacter `ν` of `T`, let
`q : G ⟶ Q` be a quotient by `B` on which `G` acts by left translation, and let `e` extend the
`νj`-orbit of `g·x₀`. If the limit `e(0)` is `n·x₀` for a point `n` normalizing `T`, then
`g ∈ B n B`. -/
theorem exists_eq_mul_mul_of_mem_normalizerPoints [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : B ⟶ G) (j : T.toGrp ⟶ G) {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    (a : SchemeAction G Q)
    (hact : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      a.act g (h ≫ q) = (g * h) ≫ q)
    (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier V)
    [IsSeparated Q.hom] [Surjective q.left] [Flat q.left] [QuasiCompact q.left]
    (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ T.toGrp)
    (hP : (parabolic (ν ≫ j)).IsRepresentedBy i)
    (n g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (hnN : n ∈ normalizerPoints j)
    {e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗
      AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ Q}
    (he : (a.restrict (ν ≫ j)).IsGmOrbitExtension (g ≫ q) e)
    (hn : evalZero e = n ≫ q) :
    ∃ b₁ b₂ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X,
      g = (b₁ ≫ i.hom.hom) * n * (b₂ ≫ i.hom.hom) := by
  obtain ⟨σ, hσ⟩ := hnN
  have : Mono i.hom.hom := hP.1
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  -- The opposite cocharacter `χ⁻¹` and its contracting subgroup `U(χ⁻¹)`.
  let κ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ T.toGrp :=
    CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ ν
  let iU := Affine.unipotentHom (κ ≫ j)
  have hU : (unipotent (κ ≫ j)).IsRepresentedBy iU := Affine.isRepresentedBy_unipotentHom _
  have hcell := oppositeCellStatement k G (ν ≫ j) _ B iU i
    (by simpa only [κ, Category.assoc] using hU) hP
  -- The conjugated cocharacter `ψ = n⁻¹ χ n` still factors through `T`.
  let ρ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ T.toGrp :=
    ν ≫ CommGroupScheme.groupHom σ.symm.hom
  have hψ : (ρ ≫ j) ≫ (G.innerIso n).hom = ν ≫ j := by
    rw [Category.assoc, Category.assoc, hσ]
    change ν ≫ CommGroupScheme.groupHom (σ.symm.hom ≫ σ.hom) ≫ j = ν ≫ j
    rw [Iso.symm_hom, Iso.inv_hom_id]
    rfl
  have hψP : SubgroupFunctor.range (ρ ≫ j) ≤ SubgroupFunctor.range i := by
    rw [hP.2]
    exact fun V x hx => centralizer_le_parabolic _ V (range_comp_le_centralizer_comp j ρ ν V hx)
  have hψU : (SubgroupFunctor.range iU).IsNormalizedBy (SubgroupFunctor.range (ρ ≫ j)) := by
    rw [hU.2]
    exact unipotent_isNormalizedBy_range_of_common_commutativeGroup j ρ κ
  exact exists_eq_mul_mul i iU q a hact hfib hcell (ν ≫ j) (ρ ≫ j) n g hψ hP.2.ge hψP hψU he hn

end BorelPair

end Langlands.GroupScheme.Dynamic.BruhatCellLimit
