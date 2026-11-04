import Langlands.GroupScheme.TorusFixedQuotientPoints
import Langlands.GroupScheme.Absolute.TorusFixedCosetBound
import Langlands.GroupScheme.Rational.MinimalParabolicContainment
import Langlands.GroupScheme.Dynamic.FlagQuotientSchemeAction
import Langlands.GroupScheme.ProjectiveOrbitRationalPoints
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof

/-! # Nonidentity normalizers from actual proper homogeneous quotients -/

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

/-- Two distinct fixed cosets with known rational lifts give an actual
normalizer point with nonidentity class. No surjectivity of rational lifts
for other quotient sections is needed. -/
def nonidentityNormalizerOfFixedCosets
    (i : T.toGrp ⟶ G) (j : P ⟶ G) (q : G.X ⟶ Q)
    (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier V)
    (hi : IsMaximalTorus i) (hj : IsClosedSubgroup j)
    (f : T.toGrp ⟶ P) (hf : f ≫ j = i)
    (hconj : MaximalToriAreConjugate P)
    (hc : centralizerPoints i ≤
      (SubgroupFunctor.range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (g₁ g₂ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hfixed₁ : ∀ (V : Over (Spec (CommRingCat.of k))) (t : V ⟶ T.toGrp.X),
      ((t ≫ i.hom.hom) * G.constantPoint g₁ V) ≫ q = G.constantPoint g₁ V ≫ q)
    (hfixed₂ : ∀ (V : Over (Spec (CommRingCat.of k))) (t : V ⟶ T.toGrp.X),
      ((t ≫ i.hom.hom) * G.constantPoint g₂ V) ≫ q = G.constantPoint g₂ V ≫ q)
    (hne : g₁ ≫ q ≠ g₂ ≫ q) :
    {n : normalizerPoints i // (QuotientGroup.mk n : relativeWeylGroup i) ≠ 1} := by
  apply Classical.choice
  obtain ⟨n₁, hn₁⟩ := exists_normalizer_representative_of_torus_fixed_coset
    i j q hfib hi hj f hf hconj g₁ hfixed₁
  obtain ⟨n₂, hn₂⟩ := exists_normalizer_representative_of_torus_fixed_coset
    i j q hfib hi hj f hf hconj g₂ hfixed₂
  refine ⟨⟨n₁⁻¹ * n₂, ?_⟩⟩
  intro h
  have heq : (QuotientGroup.mk n₁ : relativeWeylGroup i) = QuotientGroup.mk n₂ := by
    apply inv_mul_eq_one.mp
    simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using h
  apply hne
  have he := congrArg (relativeWeylCosetMap i j q hfib hc) heq
  simpa only [relativeWeylCosetMap_mk, hn₁, hn₂] using he

/-- A nonfixed rational section of a supplied proper homogeneous quotient
produces a nonidentity rational Weyl class. The exact line stabilizer and
internal maximal-torus conjugacy, torus factor and centralizer containment
remain explicit geometric inputs. -/
def nonidentityNormalizerOfNonfixedProperFlagQuotient
    [IsAlgClosed k] [LocallyOfFiniteType G.X.hom]
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    (j : P ⟶ G) (hj : IsClosedSubgroup j)
    (f : T.toGrp ⟶ P) (hf : f ≫ j = i)
    (hc : centralizerPoints i ≤
      (SubgroupFunctor.range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
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
  let p := FlagCore.twoTorusFixedOrbitLines he ho hdiag g hg'
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
  refine ⟨nonidentityNormalizerOfFixedCosets i j q hfib hi hj
    f hf hconj hc
    p.first p.second (hfixed p.first p.first_fixed) (hfixed p.second p.second_fixed) ?_⟩
  intro heq
  exact p.not_smul ((FlagCore.quotient_eq_iff_orbitVec_smul ρ l j hstab q hfib
    p.second p.first).mp heq.symm)

namespace Dynamic

/-- The dynamic-parabolic specialization supplies the torus factor and
centralizer containment to the generic proper quotient construction. -/
def nonidentityNormalizerOfNonfixedProperFlagQuotient
    [IsAlgClosed k] [LocallyOfFiniteType G.X.hom]
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ T.toGrp)
    (j : P ⟶ G) (hj : IsClosedSubgroup j)
    (hP : (parabolic (χ ≫ i)).IsRepresentedBy j)
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
    (hg : ¬ ((flagQuotientSchemeAction G (SubgroupFunctor.range j) q hfib).restrict i).IsFixed
      (g ≫ q)) :
    {w : normalizerPoints i // (QuotientGroup.mk w : relativeWeylGroup i) ≠ 1} := by
  have hc : centralizerPoints i ≤
      (SubgroupFunctor.range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    rw [← torusCentralizer_carrier_base i, hP.2]
    exact ((torusCentralizer_le_dynamicCentralizer i χ).trans
      (centralizer_le_parabolic (χ ≫ i))) _
  exact Langlands.GroupScheme.nonidentityNormalizerOfNonfixedProperFlagQuotient i hi j hj
    (parabolicTorusFactor i χ hP) (parabolicTorusFactor_comp i χ hP) hc hconj q
    hfib n ρ l hstab g hg

end Dynamic

end Langlands.GroupScheme
