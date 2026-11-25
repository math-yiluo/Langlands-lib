import Langlands.GroupScheme.Rational.MaximalSplitGeneratedReductive
import Langlands.GroupScheme.Rational.NormalizerGaloisAction
import Langlands.GroupScheme.CentralIsogeny.CorootCompatibility
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # Transport of reflections and root data along a field extension

For a field extension `K / k`, this module moves two kinds of data on a torus `S` over `k` to
its base change `S_K`.

* (A3a) `IsNormalizingPoint.baseChange_latticeReflection`: a rational point that normalizes
  `t : S ⟶ H` through the lattice reflection of `(a, ν)` still does so after base change, through
  the lattice reflection of the base-changed pair.
* `nonmultipliableBaseChange K R`: the base change to `K` of the nonmultipliable elements of a
  set `R` of characters, i.e. the image of `{c ∈ R | 2 • c ∉ R}` under
  `characterLattice.baseChange`.
* (A3b) `baseChange_rootData`: the combinatorial clauses on a set of roots `R`, a finite set `D`
  and cocharacters `lam`, `ν d` over `k` give the corresponding clauses over `K`, in the form used
  by `MaximalSplitGeneratedReductive`, with root set `nonmultipliableBaseChange K R`. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.MaximalSplitSubgroup

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))} {H : GroupScheme (Spec (CommRingCat.of k))}

local notation "bc" => algebraBaseMap k K

variable (K) in
/-- The base change to `K` of the nonmultipliable elements of a set `R` of characters of `S`:
the image under `characterLattice.baseChange` of `{c ∈ R | 2 • c ∉ R}`. -/
def nonmultipliableBaseChange (R : Set (characterLattice S)) :
    Set (characterLattice ((CommGroupScheme.baseChange bc).obj S)) :=
  characterLattice.baseChange bc S '' {c | c ∈ R ∧ (2 : ℤ) • c ∉ R}

theorem mem_nonmultipliableBaseChange_iff (R : Set (characterLattice S))
    (χ : characterLattice ((CommGroupScheme.baseChange bc).obj S)) :
    χ ∈ nonmultipliableBaseChange K R ↔
      ∃ c, (c ∈ R ∧ (2 : ℤ) • c ∉ R) ∧ characterLattice.baseChange bc S c = χ :=
  Iff.rfl

/-- For a split torus, the base change of `c` is a base-changed nonmultipliable element of `R`
exactly when `c` is a nonmultipliable element of `R`. -/
theorem baseChange_mem_nonmultipliableBaseChange_iff (hT : IsSplitTorus S.toGrp)
    (R : Set (characterLattice S)) (c : characterLattice S) :
    characterLattice.baseChange bc S c ∈ nonmultipliableBaseChange K R ↔
      c ∈ R ∧ (2 : ℤ) • c ∉ R :=
  (hT.characterLattice_baseChange_bijective bc S).injective.mem_set_image

/-- Base change of the lattice reflection of `(a, ν)` is the lattice reflection of the
base-changed pair. -/
theorem baseChange_mapIso_latticeReflectionIso (a : characterLattice S)
    (ν : cocharacterLattice S) (h : latticePairing S a ν = 2) :
    (CommGroupScheme.baseChange bc).mapIso (latticeReflectionIso a ν h) =
      latticeReflectionIso (characterLattice.baseChange bc S a)
        (cocharacterLattice.baseChange bc S ν) ((latticePairing_baseChange bc S a ν).trans h) := by
  apply Iso.ext
  rw [Functor.mapIso_hom, latticeReflectionIso_hom, latticeReflectionIso_hom,
    characterLattice.baseChange_apply]
  change (CommGroupScheme.baseChange bc).map (𝟙 S - a ≫ ν) =
    𝟙 _ - ((CommGroupScheme.baseChange bc).map a ≫ (Gm.commBaseChangeIso bc).hom) ≫
      ((Gm.commBaseChangeIso bc).inv ≫ (CommGroupScheme.baseChange bc).map ν)
  rw [Functor.map_sub, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_assoc]

/-- **(A3a)** A rational point normalizing `t` through the lattice reflection of `(a, ν)`
normalizes the base change of `t` through the lattice reflection of the base-changed pair. -/
theorem _root_.Langlands.GroupScheme.IsNormalizingPoint.baseChange_latticeReflection
    (t : S.toGrp ⟶ H) (a : characterLattice S) (ν : cocharacterLattice S)
    (h : latticePairing S a ν = 2) {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X}
    (hn : IsNormalizingPoint t n (latticeReflectionIso a ν h)) :
    IsNormalizingPoint ((GroupScheme.baseChange bc).map t) (baseChangeBasePoint bc H n)
      (latticeReflectionIso (characterLattice.baseChange bc S a)
        (cocharacterLattice.baseChange bc S ν)
        ((latticePairing_baseChange bc S a ν).trans h)) := by
  rw [← baseChange_mapIso_latticeReflectionIso a ν h]
  exact IsNormalizingPoint.baseChangeBasePoint bc hn

/-- Base change of characters is compatible with the reflection formula. -/
theorem characterLattice_baseChange_reflection (c d : characterLattice S)
    (ν : cocharacterLattice S) :
    characterLattice.baseChange bc S (c - latticePairing S c ν • d) =
      characterLattice.baseChange bc S c -
        latticePairing _ (characterLattice.baseChange bc S c)
          (cocharacterLattice.baseChange bc S ν) • characterLattice.baseChange bc S d := by
  rw [map_sub, map_zsmul, latticePairing_baseChange]

/-- The cone of the base-changed characters is the image of the cone. -/
theorem cone_baseChange (D : Finset (characterLattice S)) :
    cone (fun d : ↥D => characterLattice.baseChange bc S d.1) =
      (AddSubsemigroup.closure (D : Set (characterLattice S))).map
        (characterLattice.baseChange bc S).toAddHom := by
  rw [AddHom.map_mclosure]
  change AddSubsemigroup.closure (Set.range _) = _
  congr 1
  ext χ
  simp

/-- A character over `k` whose base change lies in the cone of the base-changed elements of `D`
lies in the additive subsemigroup generated by `D`, for a split torus. -/
theorem mem_closure_of_baseChange_mem_cone (hT : IsSplitTorus S.toGrp)
    (D : Finset (characterLattice S)) {c : characterLattice S}
    (hc : characterLattice.baseChange bc S c ∈
      cone (fun d : ↥D => characterLattice.baseChange bc S d.1)) :
    c ∈ AddSubsemigroup.closure (D : Set (characterLattice S)) := by
  rw [cone_baseChange] at hc
  obtain ⟨c', hc', hcc'⟩ := AddSubsemigroup.mem_map.mp hc
  have : c' = c := (hT.characterLattice_baseChange_bijective bc S).injective hcc'
  exact this ▸ hc'

/-- **(A3b)** Transport of the root data of the generated-subgroup argument of
`MaximalSplitGeneratedReductive` from `k` to `K`. For a split torus `S` over `k`, a
negation-stable set `R` of characters, a subset
`R' ⊆ R`, a finite set `D`, a generic cocharacter `lam` and cocharacters `ν d` with the listed
properties, the base-changed data `aK`, `νK`, `lamK` and
`ΦK = nonmultipliableBaseChange K R = ψ '' {c ∈ R | 2 • c ∉ R}` (with
`ψ = characterLattice.baseChange bc S`) satisfy the seven clauses used over `K`. -/
theorem baseChange_rootData (hT : IsSplitTorus S.toGrp) (R R' : Set (characterLattice S))
    (hR' : R' ⊆ R) (hneg : ∀ c ∈ R, -c ∈ R) (D : Finset (characterLattice S))
    (lam : cocharacterLattice S) (ν : ∀ d ∈ D, cocharacterLattice S)
    (hpos : ∀ d ∈ D, 0 < latticePairing S d lam)
    (hgen : ∀ c ∈ R, latticePairing S c lam ≠ 0)
    (hclos : ∀ c ∈ R, c ∈ AddSubsemigroup.closure (D : Set (characterLattice S)) →
      (2 : ℤ) • c ∉ R)
    (hsep : ∀ d₀ ∈ D, ∃ mu : cocharacterLattice S, latticePairing S d₀ mu = 0 ∧
      ∀ e ∈ D, e ≠ d₀ → 0 < latticePairing S e mu)
    (hν : ∀ d (hd : d ∈ D), latticePairing S d (ν d hd) = 2)
    (hrefl : ∀ Q : characterLattice S → Prop, (∀ d ∈ D, Q d) →
      (∀ d (hd : d ∈ D), ∀ c ∈ R, (2 : ℤ) • c ∉ R → Q c →
        Q (c - latticePairing S c (ν d hd) • d)) →
      ∀ c ∈ R, (2 : ℤ) • c ∉ R → Q c)
    (hred : ∀ α ∈ R, (2 : ℤ) • α ∉ R → ∀ β ∈ R, (2 : ℤ) • β ∉ R →
      (∃ m n : ℤ, m ≠ 0 ∧ m • β = n • α) → β = α ∨ β = -α) :
    let aK : ↥D → characterLattice ((CommGroupScheme.baseChange bc).obj S) :=
      fun d => characterLattice.baseChange bc S d.1
    let νK : ↥D → cocharacterLattice ((CommGroupScheme.baseChange bc).obj S) :=
      fun d => cocharacterLattice.baseChange bc S (ν d.1 d.2)
    let lamK := cocharacterLattice.baseChange bc S lam
    let ΦK := nonmultipliableBaseChange K R
    (∀ d, 0 < latticePairing _ (aK d) lamK) ∧
      (∀ χ ∈ characterLattice.baseChange bc S '' R', latticePairing _ χ lamK ≠ 0) ∧
      (∀ d, ∃ eta, IsIsolatingCocharacter aK d eta) ∧
      (∀ d, latticePairing _ (aK d) (νK d) = 2) ∧
      (∀ χ ∈ characterLattice.baseChange bc S '' R', χ ∈ cone aK ∨ -χ ∈ cone aK → χ ∈ ΦK) ∧
      (∀ α ∈ ΦK, ∀ β ∈ ΦK, (∃ m n : ℤ, m ≠ 0 ∧ m • β = n • α) → β = α ∨ β = -α) ∧
      LiesInReflectionClosure aK νK ΦK := by
  intro aK νK lamK ΦK
  have hinj := (hT.characterLattice_baseChange_bijective bc S).injective
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨d, hd⟩
    simp only [aK, lamK, latticePairing_baseChange]
    exact hpos d hd
  · rintro _ ⟨c, hc, rfl⟩
    simp only [lamK, latticePairing_baseChange]
    exact hgen c (hR' hc)
  · rintro ⟨d, hd⟩
    obtain ⟨mu, hmu0, hmu⟩ := hsep d hd
    refine ⟨cocharacterLattice.baseChange bc S mu, ?_, ?_⟩
    · simp only [aK, latticePairing_baseChange]
      exact hmu0
    · rintro ⟨e, he⟩ hne
      simp only [aK, latticePairing_baseChange]
      exact hmu e he (fun h => hne (Subtype.ext h))
  · rintro ⟨d, hd⟩
    simp only [aK, νK, latticePairing_baseChange]
    exact hν d hd
  · rintro _ ⟨c, hc, rfl⟩ hcone
    refine (baseChange_mem_nonmultipliableBaseChange_iff hT R c).2 ⟨hR' hc, ?_⟩
    rcases hcone with hcone | hcone
    · exact hclos c (hR' hc) (mem_closure_of_baseChange_mem_cone hT D hcone)
    · rw [← map_neg] at hcone
      have h2 := hclos (-c) (hneg c (hR' hc)) (mem_closure_of_baseChange_mem_cone hT D hcone)
      intro h2c
      apply h2
      rw [smul_neg]
      exact hneg _ h2c
  · intro α hα β hβ hmn'
    obtain ⟨a, ⟨ha, ha2⟩, rfl⟩ := (mem_nonmultipliableBaseChange_iff R α).1 hα
    obtain ⟨b, ⟨hb, hb2⟩, rfl⟩ := (mem_nonmultipliableBaseChange_iff R β).1 hβ
    obtain ⟨m, n, hm, hmn⟩ := hmn'
    rw [← map_zsmul, ← map_zsmul] at hmn
    rcases hred a ha ha2 b hb hb2 ⟨m, n, hm, hinj hmn⟩ with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (map_neg _ _)
  · intro P hP hstep χ hχ
    obtain ⟨c, ⟨hc, hc2⟩, rfl⟩ := (mem_nonmultipliableBaseChange_iff R χ).1 hχ
    refine hrefl (fun c => P (characterLattice.baseChange bc S c)) (fun d hd => hP ⟨d, hd⟩)
      ?_ c hc hc2
    intro d hd c' _ _ hQ
    rw [characterLattice_baseChange_reflection]
    exact hstep ⟨d, hd⟩ _ hQ

end Langlands.GroupScheme.MaximalSplitSubgroup
