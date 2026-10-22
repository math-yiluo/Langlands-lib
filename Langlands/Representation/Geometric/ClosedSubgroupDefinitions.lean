import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Filtration.Definitions
import Mathlib.RepresentationTheory.Rep.Res

/-! Concrete functors and orbit data for closed-subgroup Mackey filtrations. -/

noncomputable section
open CategoryTheory

namespace Langlands.Geometric

universe uR uG uV

variable {R : Type uR} [CommRing R]
  {G : Type uG} [Group G]

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Restriction to `Q` of compact induction with an arbitrary algebraic
covariance representation of `P`. The induced functions are smooth by
construction; the covariance representation need not be smooth. -/
def rawRestrictedCompactInduction (P Q : Subgroup G) :
    Rep.{uV} R P ⥤ Rep.{max uG uV} R Q :=
  Induction.compactInductionFunctor P ⋙
    ObjectProperty.ι (fun A : Rep.{max uG uV} R G => IsSmooth A.ρ) ⋙
    Rep.resFunctor Q.subtype

/-- The existing smooth-input specialization of restricted compact induction. -/
def restrictedCompactInduction (P Q : Subgroup G) :
    Induction.SmoothRep.{uR, uG, uV} R P ⥤ Rep.{max uG uV} R Q :=
  ObjectProperty.ι (fun A : Rep.{uV} R P => IsSmooth A.ρ) ⋙
    rawRestrictedCompactInduction P Q

/-- The subgroup `Q ∩ w P w⁻¹`, viewed as a subgroup of `Q`. -/
def orbitStabilizer (P Q : Subgroup G) (w : G) : Subgroup Q :=
  P.comap ((MulAut.conj w⁻¹).toMonoidHom.comp Q.subtype)

/-- Conjugation from the orbit stabilizer into the inducing subgroup. -/
def stabilizerToInducing (P Q : Subgroup G) (w : G) :
    orbitStabilizer P Q w →* P where
  toFun q := ⟨(MulAut.conj w⁻¹) (q.val : G), q.property⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (MulAut.conj w⁻¹)
  map_mul' q r := by
    apply Subtype.ext
    exact map_mul (MulAut.conj w⁻¹) (q.val : G) (r.val : G)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem stabilizerToInducing_apply (P Q : Subgroup G) (w : G)
    (q : orbitStabilizer P Q w) :
    (stabilizerToInducing P Q w q : G) = w⁻¹ * (q.val : G) * w := by
  simp [stabilizerToInducing]

/-- The actual orbit-piece functor: conjugated restriction followed by compact
induction from `Q ∩ w P w⁻¹` to `Q`. -/
def orbitPiece (P Q : Subgroup G) (w : G) :
    Induction.SmoothRep.{uR, uG, uV} R P ⥤ Rep.{max uG uV} R Q :=
  ObjectProperty.ι (fun A : Rep.{uV} R P => IsSmooth A.ρ) ⋙
    Rep.resFunctor (stabilizerToInducing P Q w) ⋙
    Induction.compactInductionFunctor (orbitStabilizer P Q w) ⋙
    ObjectProperty.ι (fun A : Rep.{max uG uV} R Q => IsSmooth A.ρ)

/-- The actual `Q`-orbit of `P w⁻¹` in `P \ G`. -/
def cosetOrbit (P Q : Subgroup G) (w : G) : Set (Induction.LeftQuotient P) :=
  Set.range (fun q : Q => Induction.quotientMap P (w⁻¹ * (q : G)))

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem cosetOrbit_right_invariant (P Q : Subgroup G) (w : G) (q : Q)
    {x : Induction.LeftQuotient P} (hx : x ∈ cosetOrbit P Q w) :
    Induction.quotientRight P (q : G) x ∈ cosetOrbit P Q w := by
  obtain ⟨r, rfl⟩ := hx
  refine ⟨r * q, ?_⟩
  change Induction.quotientMap P (w⁻¹ * ((r : G) * (q : G))) =
    Induction.quotientMap P ((w⁻¹ * (r : G)) * (q : G))
  rw [mul_assoc]

/-- Compactly induced functions supported in an actual invariant subset of
`P \ G`, for arbitrary algebraic covariance representations. -/
def rawSupportSubfunctor (P Q : Subgroup G) (U : Set (Induction.LeftQuotient P))
    (hU : ∀ (q : Q) (x : Induction.LeftQuotient P), x ∈ U →
      Induction.quotientRight P (q : G) x ∈ U) :
    RepSubfunctor (rawRestrictedCompactInduction.{uR, uG, uV} (R := R) P Q) where
  obj A :=
    { toSubmodule :=
        { carrier := {f | ∀ x : G, Induction.eval P A.ρ f.val x ≠ 0 →
              Induction.quotientMap P x ∈ U}
          zero_mem' := by
            intro x hx
            exact False.elim (hx rfl)
          add_mem' := by
            intro f g hf hg x hx
            by_cases hfx : Induction.eval P A.ρ f.val x = 0
            · apply hg x
              intro hgx
              apply hx
              change Induction.eval P A.ρ f.val x +
                Induction.eval P A.ρ g.val x = 0
              rw [hfx, hgx, add_zero]
            · exact hf x hfx
          smul_mem' := by
            intro a f hf x hx
            apply hf x
            intro hfx
            apply hx
            change a • Induction.eval P A.ρ f.val x = 0
            rw [hfx, smul_zero] }
      apply_mem_toSubmodule := by
        intro q f hf x hx
        have hu := hU q⁻¹ (Induction.quotientMap P (x * (q : G)))
          (hf (x * (q : G)) hx)
        simpa [Induction.quotientRight, Induction.quotientMap, mul_assoc] using hu }
  map_mem := by
    intro A B f v hv x hx
    apply hv x
    intro hvx
    apply hx
    change f.hom (Induction.eval P A.ρ v.val x) = 0
    rw [hvx, map_zero]

/-- Restriction of the raw support subfunctor to smooth inducing inputs. -/
def supportSubfunctor (P Q : Subgroup G) (U : Set (Induction.LeftQuotient P))
    (hU : ∀ (q : Q) (x : Induction.LeftQuotient P), x ∈ U →
      Induction.quotientRight P (q : G) x ∈ U) :
    RepSubfunctor (restrictedCompactInduction.{uR, uG, uV} (R := R) P Q) where
  obj A := (rawSupportSubfunctor P Q U hU).obj A.obj
  map_mem := by
    intro A B f v hv
    exact (rawSupportSubfunctor P Q U hU).map_mem f.hom hv

/-- An ordered finite enumeration of actual double-coset orbits.
The open-initial-union condition is geometric input, not an assumed
representation-theoretic conclusion. -/
structure OrderedDoubleCosets (P Q : Subgroup G) (n : ℕ) where
  representative : Fin n → G
  covers : ∀ x : Induction.LeftQuotient P,
    ∃ i, x ∈ cosetOrbit P Q (representative i)
  disjoint : Pairwise (fun i j =>
    Disjoint (cosetOrbit P Q (representative i)) (cosetOrbit P Q (representative j)))
  initial_open : ∀ k : Fin (n + 1), IsOpen
    {x | ∃ i : Fin n, i.val < k.val ∧ x ∈ cosetOrbit P Q (representative i)}

namespace OrderedDoubleCosets

variable {P Q : Subgroup G} {n : ℕ}

/-- The union of the first `k` orbits in the specified order. -/
def initialOrbits (s : OrderedDoubleCosets P Q n) (k : Fin (n + 1)) :
    Set (Induction.LeftQuotient P) :=
  {x | ∃ i : Fin n, i.val < k.val ∧ x ∈ cosetOrbit P Q (s.representative i)}

omit [IsTopologicalGroup G] in
theorem initialOrbits_right_invariant (s : OrderedDoubleCosets P Q n)
    (k : Fin (n + 1)) (q : Q) {x : Induction.LeftQuotient P}
    (hx : x ∈ s.initialOrbits k) :
    Induction.quotientRight P (q : G) x ∈ s.initialOrbits k := by
  obtain ⟨i, hi, hx⟩ := hx
  exact ⟨i, hi, cosetOrbit_right_invariant P Q (s.representative i) q hx⟩

omit [IsTopologicalGroup G] in
theorem initialOrbits_monotone (s : OrderedDoubleCosets P Q n) :
    Monotone s.initialOrbits := by
  intro i j hij x hx
  obtain ⟨k, hk, hx⟩ := hx
  exact ⟨k, lt_of_lt_of_le hk hij, hx⟩

omit [IsTopologicalGroup G] in
theorem initialOrbits_zero (s : OrderedDoubleCosets P Q n) :
    s.initialOrbits 0 = ∅ := by
  ext x
  simp [initialOrbits]

omit [IsTopologicalGroup G] in
theorem initialOrbits_top (s : OrderedDoubleCosets P Q n) :
    s.initialOrbits (Fin.last n) = Set.univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨i, hi⟩ := s.covers x
    exact ⟨i, i.isLt, hi⟩

/-- The natural filtration by support in initial orbit unions. Monotonicity
follows from containment, the zero endpoint from the empty union, and the full
endpoint from the orbit cover. Graded-piece isomorphisms are separate. -/
def rawSupportFiltration (s : OrderedDoubleCosets P Q n) :
    RepFunctorFiltration (rawRestrictedCompactInduction.{uR, uG, uV} (R := R) P Q) n where
  step k := rawSupportSubfunctor P Q (s.initialOrbits k)
    (fun q _ hx => s.initialOrbits_right_invariant k q hx)
  monotone A := by
    intro i j hij f hf x hx
    exact s.initialOrbits_monotone hij (hf x hx)
  zero A := by
    apply le_antisymm
    · intro f hf
      change f = 0
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      funext x
      by_contra hx
      have hu := hf x hx
      simp [s.initialOrbits_zero] at hu
    · exact bot_le
  top A := by
    apply le_antisymm le_top
    intro f _ x _
    rw [s.initialOrbits_top]
    trivial

/-- The existing smooth-input support filtration, obtained by restriction
of the raw construction without changing the support spaces or order. -/
def supportFiltration (s : OrderedDoubleCosets P Q n) :
    RepFunctorFiltration (restrictedCompactInduction.{uR, uG, uV} (R := R) P Q) n where
  step k := supportSubfunctor P Q (s.initialOrbits k)
    (fun q _ hx => s.initialOrbits_right_invariant k q hx)
  monotone A := s.rawSupportFiltration.monotone A.obj
  zero A := s.rawSupportFiltration.zero A.obj
  top A := s.rawSupportFiltration.top A.obj

end OrderedDoubleCosets

end Langlands.Geometric
