import Langlands.GroupScheme.CentralizerSeparatedOrbitLines
import Langlands.GroupScheme.TorusFixedQuotientPoints
import Langlands.GroupScheme.Absolute.TorusFixedCosetBound
import Langlands.GroupScheme.Dynamic.FlagQuotientSchemeAction
import Langlands.GroupScheme.ProjectiveOrbitRationalPoints
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof

/-! # Nonidentity normalizers from distinct extreme weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {G P : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {Q : Over (Spec (CommRingCat.of k))}

/-- A nonfixed rational section of a supplied proper homogeneous quotient
gives a nonidentity normalizer class. The two extreme orbit lines have distinct
cocharacter weights, so no centralizer containment in the stabilizer is needed. -/
def nonidentityNormalizerOfWeightSeparatedProperQuotient
    [IsAlgClosed k] [LocallyOfFiniteType G.X.hom]
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    (j : P ⟶ G) (hj : IsClosedSubgroup j)
    (f : T.toGrp ⟶ P) (hf : f ≫ j = i)
    (hconj : MaximalToriAreConjugate P) (q : G.X ⟶ Q)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left] [IsProper Q.hom]
    (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier V)
    (n : ℕ) (ρ : MatrixRepresentation G (Fin (n + 1))) (l : Fin (n + 1))
    (hstab : ∀ (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ G.X),
      x ∈ (SubgroupFunctor.range j).carrier V ↔
        ∃ c : Γ(V.left, ⊤)ˣ,
          (ρ.pointMatrix V x : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(V.left, ⊤)) *ᵥ
              Pi.single l 1 =
            (c : Γ(V.left, ⊤)) • (Pi.single l (1 : Γ(V.left, ⊤)) :
              Fin (n + 1) → Γ(V.left, ⊤)))
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hg : ¬ ((Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range j) q hfib).restrict i).IsFixed
      (g ≫ q)) :
    {w : normalizerPoints i // (QuotientGroup.mk w : relativeWeylGroup i) ≠ 1} := by
  apply Classical.choice
  have : Smooth T.toGrp.X.hom := IsTorus.smooth hi.1
  have he : (Pi.single l (1 : k) : Fin (n + 1) → k) ≠ 0 := by
    intro h
    exact one_ne_zero (α := k) (by simpa using congrFun h l)
  have ho : FlagCore.IsClosedOrbit
      (FlagCore.orbitVec ρ.rationalMatrix (Pi.single l 1)) := by
    intro c hc hvan
    exact ProjectiveOrbit.exists_eq_smul_orbit_of_isProper n ρ l q
      (fun V g h heq => (hstab V (g⁻¹ * h)).mp ((hfib V g h).mp heq)) c hc hvan
  obtain ⟨I, hI, A, wt, τ, hdiag, hparam⟩ :=
    FlagCore.exists_torusDiagonal torusFiniteGaloisSplitting hi ρ
  let a := Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range j) q hfib
  have hact : ∀ (V : Over (Spec (CommRingCat.of k))) (x y : V ⟶ G.X),
      a.act x (y ≫ q) = (x * y) ≫ q := by
    intro V x y
    exact Dynamic.flagQuotientSchemeAction_act_lift G (SubgroupFunctor.range j) q hfib x y
  have hg' : ¬ FlagCore.IsTorusFixed ρ.rationalMatrix τ
      (FlagCore.orbitVec ρ.rationalMatrix (Pi.single l 1) g) := by
    intro h
    exact hg ((FlagCore.isFixed_quotient_iff_isTorusFixed ρ l j hstab q hfib
      i a hact τ hparam g).mpr h)
  let p := FlagCore.centralizerSeparatedOrbitLines he ho hdiag g hg'
  have hfixed : ∀ g' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      FlagCore.IsTorusFixed ρ.rationalMatrix τ
        (FlagCore.orbitVec ρ.rationalMatrix (Pi.single l 1) g') →
      ∀ (V : Over (Spec (CommRingCat.of k))) (t : V ⟶ T.toGrp.X),
        ((t ≫ i.hom.hom) * G.constantPoint g' V) ≫ q = G.constantPoint g' V ≫ q := by
    intro g' hg' V t
    have hx := (FlagCore.isFixed_quotient_iff_isTorusFixed ρ l j hstab q hfib
      i a hact τ hparam g').mpr hg'
    have heq := hx V (Over.homMk V.hom (by simp)) t
    rw [← Category.assoc] at heq
    change (a.restrict i).act t (G.constantPoint g' V ≫ q) =
      G.constantPoint g' V ≫ q at heq
    rwa [SchemeAction.restrict_act, hact] at heq
  obtain ⟨n₁, hn₁⟩ := exists_normalizer_representative_of_torus_fixed_coset
    i j q hfib hi hj f hf hconj p.first (hfixed p.first p.first_fixed)
  obtain ⟨n₂, hn₂⟩ := exists_normalizer_representative_of_torus_fixed_coset
    i j q hfib hi hj f hf hconj p.second (hfixed p.second p.second_fixed)
  refine ⟨⟨n₁ * n₂⁻¹, ?_⟩⟩
  intro h
  have hx : n₁.val * n₂.val⁻¹ ∈ centralizerPoints i :=
    (QuotientGroup.eq_one_iff (n₁ * n₂⁻¹)).mp h
  rw [← torusCentralizer_carrier_base i] at hx
  have hcomm : ∀ s, Commute (n₁.val * n₂.val⁻¹) (τ s) := by
    intro s
    obtain ⟨t, ht⟩ : ∃ t : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.toGrp.X,
        t ≫ i.hom.hom = τ s := by
      have hs : τ s ∈ Set.range τ := ⟨s, rfl⟩
      rwa [hparam] at hs
    simpa only [Category.id_comp, ht] using
      (mem_torusCentralizer i).mp hx _ (𝟙 _) t
  apply p.separated (n₁.val * n₂.val⁻¹) hcomm
  obtain ⟨c, hc⟩ := (FlagCore.quotient_eq_iff_orbitVec_smul ρ l j hstab q hfib
    n₁.val p.first).mp hn₁
  obtain ⟨d, hd⟩ := (FlagCore.quotient_eq_iff_orbitVec_smul ρ l j hstab q hfib
    p.second n₂.val).mp hn₂.symm
  have hmul : (n₁.val * n₂.val⁻¹) * n₂.val = n₁.val := by group
  refine ⟨c * d, ?_⟩
  calc
    FlagCore.orbitVec ρ.rationalMatrix (Pi.single l 1) p.first =
        c • FlagCore.orbitVec ρ.rationalMatrix (Pi.single l 1) n₁.val := hc
    _ = c • ((ρ.rationalMatrix (n₁.val * n₂.val⁻¹) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ
          FlagCore.orbitVec ρ.rationalMatrix (Pi.single l 1) n₂.val) := by
      rw [← FlagCore.orbitVec_mul, hmul]
    _ = (c * d) • ((ρ.rationalMatrix (n₁.val * n₂.val⁻¹) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ
          FlagCore.orbitVec ρ.rationalMatrix (Pi.single l 1) p.second) := by
      rw [hd, mulVec_smul, smul_smul]

end Langlands.GroupScheme
