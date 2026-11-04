import Langlands.GroupScheme.TorusFixedOrbitLines
import Langlands.GroupScheme.FlagCoreTorus
import Langlands.GroupScheme.SchemeActionRationalPoints

/-! # From torus-fixed orbit lines to all-test fixed quotient points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.FlagCore

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {G B : GroupScheme (Spec (CommRingCat.of k))}
    {m : Type} [Fintype m] [DecidableEq m]
    (ρ : MatrixRepresentation G m) (j : m) (b : B ⟶ G)
    (hstab : ∀ (Z : Over (Spec (CommRingCat.of k))) (x : Z ⟶ G.X),
      x ∈ (SubgroupFunctor.range b).carrier Z ↔
        ∃ c : Γ(Z.left, ⊤)ˣ,
          (ρ.pointMatrix Z x : Matrix m m Γ(Z.left, ⊤)) *ᵥ Pi.single j 1 =
            (c : Γ(Z.left, ⊤)) • (Pi.single j (1 : Γ(Z.left, ⊤)) :
              m → Γ(Z.left, ⊤)))
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    (hfib : ∀ (Z : Over (Spec (CommRingCat.of k))) (g h : Z ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier Z)

include hstab hfib

/-- The exact quotient fibers of an all-test line stabilizer are exactly
proportionality of the corresponding rational orbit vectors. -/
theorem quotient_eq_iff_orbitVec_smul
    (g h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    g ≫ q = h ≫ q ↔
      ∃ c : k, orbitVec ρ.rationalMatrix (Pi.single j 1) h =
        c • orbitVec ρ.rationalMatrix (Pi.single j 1) g := by
  rw [hfib, hstab, exists_unit_pointMatrix_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hh : ρ.rationalMatrix h =
        ρ.rationalMatrix g * ρ.rationalMatrix (g⁻¹ * h) := by
      rw [← map_mul]
      congr 1
      group
    unfold orbitVec
    rw [hh, Units.val_mul, ← mulVec_mulVec, hc, mulVec_smul]
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    unfold orbitVec at hc
    rw [map_mul, map_inv, Units.val_mul, ← mulVec_mulVec, hc, mulVec_smul,
      mulVec_mulVec, Units.inv_mul, one_mulVec]

variable [IsAlgClosed k]
    {T : GroupScheme (Spec (CommRingCat.of k))} (i : T ⟶ G)
    [Smooth T.X.hom] [IsSeparated Q.hom]
    (a : SchemeAction G Q)
    (hact : ∀ (Z : Over (Spec (CommRingCat.of k))) (g h : Z ⟶ G.X),
      a.act g (h ≫ q) = (g * h) ≫ q)
    {I : Type*}
    (τ : (I → kˣ) → (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))
    (hparam : Set.range τ =
      Set.range fun z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.X =>
        z ≫ i.hom.hom)

include hact hparam

/-- For a smooth acting group over an algebraically closed field, the
rational fixed-line condition is exactly all-test fixedness of its quotient
section. No reducedness of the quotient is required. -/
theorem isFixed_quotient_iff_isTorusFixed
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    (a.restrict i).IsFixed (g ≫ q) ↔
      IsTorusFixed ρ.rationalMatrix τ
        (orbitVec ρ.rationalMatrix (Pi.single j 1) g) := by
  rw [(a.restrict i).isFixed_iff_rationalPoints]
  constructor
  · intro hg s
    obtain ⟨z, hz⟩ : ∃ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.X,
        z ≫ i.hom.hom = τ s := by
      have hmem : τ s ∈ Set.range τ := ⟨s, rfl⟩
      rw [hparam] at hmem
      exact hmem
    have hfix := hg z
    rw [SchemeAction.restrict_act, hact] at hfix
    have hline := (quotient_eq_iff_orbitVec_smul ρ j b hstab q hfib
      g ((z ≫ i.hom.hom) * g)).mp hfix.symm
    simpa only [orbitVec_mul, hz] using hline
  · intro hg z
    obtain ⟨s, hs⟩ : ∃ s, τ s = z ≫ i.hom.hom := by
      have hmem : z ≫ i.hom.hom ∈ Set.range
          (fun z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.X =>
            z ≫ i.hom.hom) := ⟨z, rfl⟩
      rw [← hparam] at hmem
      exact hmem
    rw [SchemeAction.restrict_act, hact]
    apply Eq.symm
    apply (quotient_eq_iff_orbitVec_smul ρ j b hstab q hfib
      g ((z ≫ i.hom.hom) * g)).mpr
    simpa only [orbitVec_mul, hs] using hg s

variable [Fintype I]

/-- Two extreme-weight contractions give two distinct actual all-test fixed
rational sections of a supplied homogeneous quotient. -/
noncomputable def twoTorusFixedQuotientPoints
    (ho : IsClosedOrbit (orbitVec ρ.rationalMatrix (Pi.single j 1)))
    {P : GL m k} {wt : m → I → ℤ}
    (hdiag : ∀ s, (ρ.rationalMatrix (τ s) : Matrix m m k) =
      (P : Matrix m m k) * diagonal (fun l => (charValue wt s l : k)) *
        (↑P⁻¹ : Matrix m m k))
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hg : ¬ (a.restrict i).IsFixed (g ≫ q)) :
    Bool ↪ {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q //
      (a.restrict i).IsFixed x} := by
  classical
  have he : (Pi.single j (1 : k) : m → k) ≠ 0 := by
    intro h
    exact one_ne_zero (α := k) (by simpa using congrFun h j)
  have hg' : ¬ IsTorusFixed ρ.rationalMatrix τ
      (orbitVec ρ.rationalMatrix (Pi.single j 1) g) :=
    fun h => hg ((isFixed_quotient_iff_isTorusFixed ρ j b hstab q hfib
      i a hact τ hparam g).mpr h)
  let p := twoTorusFixedOrbitLines he ho hdiag g hg'
  let x₁ : {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q //
      (a.restrict i).IsFixed x} :=
    ⟨p.first ≫ q, (isFixed_quotient_iff_isTorusFixed ρ j b hstab q hfib
      i a hact τ hparam p.first).mpr p.first_fixed⟩
  let x₂ : {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q //
      (a.restrict i).IsFixed x} :=
    ⟨p.second ≫ q, (isFixed_quotient_iff_isTorusFixed ρ j b hstab q hfib
      i a hact τ hparam p.second).mpr p.second_fixed⟩
  have hne : x₁ ≠ x₂ := by
    intro h
    exact p.not_smul ((quotient_eq_iff_orbitVec_smul ρ j b hstab q hfib
      p.second p.first).mp (congrArg Subtype.val h).symm)
  refine ⟨fun c => if c then x₁ else x₂, ?_⟩
  intro c d h
  cases c <;> cases d
  · rfl
  · exact False.elim (hne h.symm)
  · exact False.elim (hne h)
  · rfl

end Langlands.GroupScheme.FlagCore
