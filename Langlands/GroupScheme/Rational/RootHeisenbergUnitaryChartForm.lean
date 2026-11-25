import Langlands.GroupScheme.Rational.RootHeisenbergChartPoints
import Langlands.Geometry.Building.RootUnitaryHeisenbergAssembly
import Mathlib.LinearAlgebra.QuadraticForm.Basis

/-! # The chart form of unitary root coordinates

Let `U = U_a` be a multipliable relative root group with Heisenberg normal form `N` and weight
vector coordinates. A rational homomorphism `φ` from the unitary parameters
`{(u, v) ∈ L² | v + σ(v) = u σ(u)}` to `U(K)` which is bijective, sends exactly the central
parameters into `U_{2a}(K)`, and intertwines the scaling by every `c ∈ Kˣ` with the action of
some point of the torus with root value `c`, has the chart form
`φ(u, v) = incl(B v + H(u, u)) * sec(A u)` with `K`-linear `A`, `B` and `K`-bilinear `H`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.RelativeRoot

variable {K : Type u} [Field K]

section Coordinates

variable {V : GroupScheme (Spec (CommRingCat.of K))} {n : ℕ}
  (e : ∀ T : Over (Spec (CommRingCat.of K)),
    (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤)))

/-- The rational point with `K`-valued vector coordinates `x`. -/
def vectorPoint (x : Fin n → K) : rationalPoints V :=
  (rationalVectorCoordinates e).symm (Multiplicative.ofAdd x)

theorem toAdd_rationalVectorCoordinates (v : rationalPoints V) :
    (rationalVectorCoordinates e v).toAdd = fun l =>
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
        ((e (Over.mk (𝟙 _)) v).toAdd l) :=
  rfl

@[simp] theorem rationalVectorCoordinates_vectorPoint (x : Fin n → K) :
    (rationalVectorCoordinates e (vectorPoint e x)).toAdd = x := by
  rw [vectorPoint, MulEquiv.apply_symm_apply, toAdd_ofAdd]

@[simp] theorem vectorPoint_toAdd (v : rationalPoints V) :
    vectorPoint e (rationalVectorCoordinates e v).toAdd = v := by
  rw [vectorPoint, ofAdd_toAdd, MulEquiv.symm_apply_apply]

theorem vectorPoint_injective : Function.Injective (vectorPoint e) := by
  intro x y h
  have := congrArg (fun v => (rationalVectorCoordinates e v).toAdd) h
  simpa using this

@[simp] theorem vectorPoint_zero : vectorPoint e (0 : Fin n → K) = 1 := by
  rw [vectorPoint, ofAdd_zero, map_one]

theorem vectorPoint_add (x y : Fin n → K) :
    vectorPoint e (x + y) = vectorPoint e x * vectorPoint e y := by
  rw [vectorPoint, vectorPoint, vectorPoint, ofAdd_add, map_mul]

theorem vectorPoint_eq_one_iff (x : Fin n → K) : vectorPoint e x = 1 ↔ x = 0 := by
  rw [← vectorPoint_zero e]
  exact (vectorPoint_injective e).eq_iff

/-- Scalar multiplication of `K`-valued coordinates, read in the coordinates on `Spec K`. -/
theorem vectorPoint_smul (c : K) (x : Fin n → K) :
    vectorPoint e (c • x) = (e (Over.mk (𝟙 _))).symm (Multiplicative.ofAdd
      ((show Γ((Over.mk (𝟙 (Spec (CommRingCat.of K)))).left, ⊤) from
        (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm c) •
        (e (Over.mk (𝟙 _)) (vectorPoint e x)).toAdd)) := by
  apply (rationalVectorCoordinates e).injective
  apply Multiplicative.toAdd.injective
  rw [rationalVectorCoordinates_vectorPoint, toAdd_rationalVectorCoordinates,
    MulEquiv.apply_symm_apply, toAdd_ofAdd]
  funext l
  have hx := congrFun (rationalVectorCoordinates_vectorPoint e x) l
  rw [toAdd_rationalVectorCoordinates] at hx
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply, hx]

/-- The value in `K` of a character on a rational point of the torus. -/
theorem rationalCharacterEval_two_nsmul {S : CommGroupScheme (Spec (CommRingCat.of K))}
    (a : characterLattice S) (t : rationalPoints S.toGrp) :
    rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm (2 • a)) t =
      rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm a) t ^ 2 := by
  have h2 : (rationalCharacters.equivCharacterLattice S).symm (2 • a) =
      2 • (rationalCharacters.equivCharacterLattice S).symm a :=
    (rationalCharacters.equivCharacterLattice S).symm.toAddMonoidHom.map_nsmul 2 a
  rw [h2, two_nsmul, rationalCharacterEval_add, sq]

/-- Rational points of the torus act on `K`-valued weight vector coordinates by the value of
the weight. -/
theorem act_vectorPoint {S : CommGroupScheme (Spec (CommRingCat.of K))}
    {b : AutomorphicAction S.toGrp V} {χ : characterLattice S}
    (he : IsWeightVectorCoordinates b χ e) (t : rationalPoints S.toGrp) (x : Fin n → K) :
    b.act t (vectorPoint e x) = vectorPoint e
      ((rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm χ) t : K) •
        x) := by
  apply (rationalVectorCoordinates e).injective
  apply Multiplicative.toAdd.injective
  rw [rationalVectorCoordinates_vectorPoint, toAdd_rationalVectorCoordinates, he.2]
  funext l
  have hx := congrFun (rationalVectorCoordinates_vectorPoint e x) l
  rw [toAdd_rationalVectorCoordinates] at hx
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, hx]
  rfl

end Coordinates

section Chart

variable {S : CommGroupScheme (Spec (CommRingCat.of K))}
    {G U U₂ : GroupScheme (Spec (CommRingCat.of K))}
    {i : S.toGrp ⟶ G} {a : characterLattice S}
    {j : U ⟶ G} {hj : (subgroup i a).IsRepresentedBy j}
    {j₂ : U₂ ⟶ G} {hj₂ : (subgroup i (2 • a)).IsRepresentedBy j₂}
    {C : DoubleRootCommutatorPairing i a hj hj₂}

namespace HeisenbergNormalForm

variable (N : HeisenbergNormalForm C) {d m : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of K)),
      (T ⟶ C.V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (e' : ∀ T : Over (Spec (CommRingCat.of K)),
      (T ⟶ U₂.X) ≃* Multiplicative (Fin m → Γ(T.left, ⊤)))

theorem chartPoint_def (x : Fin d → K) (w : Fin m → K) :
    N.chartPoint e e' x w =
      (vectorPoint e' w ≫ N.inclusion.hom.hom) * (vectorPoint e x ≫ N.sec) :=
  rfl

theorem sec_comp_quotient {T : Over (Spec (CommRingCat.of K))} (x : T ⟶ C.V.X) :
    (x ≫ N.sec) ≫ C.q.hom.hom = x := by
  rw [Category.assoc, N.sec_comp, Category.comp_id]

theorem chartPoint_comp_quotient (x : Fin d → K) (w : Fin m → K) :
    N.chartPoint e e' x w ≫ C.q.hom.hom = vectorPoint e x := by
  rw [chartPoint_def, MonObj.mul_comp, Langlands.Geometry.Building.HeisenbergUnitaryData.inclusion_comp_q, sec_comp_quotient, one_mul]

theorem chartPoint_injective {x x' : Fin d → K} {w w' : Fin m → K}
    (h : N.chartPoint e e' x w = N.chartPoint e e' x' w') : x = x' ∧ w = w' := by
  have hx : x = x' := by
    have h' := congrArg (· ≫ C.q.hom.hom) h
    simp only [chartPoint_comp_quotient] at h'
    exact vectorPoint_injective e h'
  subst hx
  refine ⟨rfl, ?_⟩
  rw [chartPoint_def, chartPoint_def] at h
  have h' := mul_right_cancel h
  let := N.mono_inclusion
  exact vectorPoint_injective e' ((cancel_mono N.inclusion.hom.hom).mp h')

theorem exists_eq_chartPoint (g : rationalPoints U) :
    ∃ (x : Fin d → K) (w : Fin m → K), g = N.chartPoint e e' x w := by
  obtain ⟨w, hw⟩ := N.exists_eq_mul_sec g
  refine ⟨(rationalVectorCoordinates e (g ≫ C.q.hom.hom)).toAdd,
    (rationalVectorCoordinates e' w).toAdd, ?_⟩
  rw [chartPoint_def, vectorPoint_toAdd, vectorPoint_toAdd]
  exact hw

theorem chartPoint_zero_zero : N.chartPoint e e' 0 0 = 1 := by
  rw [chartPoint_def, vectorPoint_zero, vectorPoint_zero, MonObj.one_comp, N.one_sec, one_mul]

/-- The points of the doubled root group are central in the root group. -/
theorem commute_inclusion [IsAffineHom G.X.hom] [Smooth G.X.hom] (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i)
    {T : Over (Spec (CommRingCat.of K))} (w : T ⟶ U₂.X) (g : T ⟶ U.X) :
    Commute (w ≫ N.inclusion.hom.hom) g := by
  apply commute_comap_double_of_noHigherRoots hS i ha hhigh hj T
  change (w ≫ N.inclusion.hom.hom) ≫ j.hom.hom ∈ (subgroup i (2 • a)).carrier T
  rw [Category.assoc, N.inclusion_comp_hom, ← hj₂.2]
  exact ⟨w, rfl⟩

/-- The cocycle of the normal form in `K`-valued coordinates. -/
def cocycleCoordinates (x y : Fin d → K) : Fin m → K :=
  (rationalVectorCoordinates e' (lift (vectorPoint e x) (vectorPoint e y) ≫ N.cocycle)).toAdd

theorem chartPoint_mul [IsAffineHom G.X.hom] [Smooth G.X.hom] (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i)
    (x x' : Fin d → K) (w w' : Fin m → K) :
    N.chartPoint e e' x w * N.chartPoint e e' x' w' =
      N.chartPoint e e' (x + x') (w + w' + N.cocycleCoordinates e e' x x') := by
  rw [chartPoint_def, chartPoint_def, chartPoint_def]
  have hc := N.commute_inclusion hS ha hhigh (vectorPoint e' w') (vectorPoint e x ≫ N.sec)
  have hsec := N.sec_mul _ (vectorPoint e x) (vectorPoint e x')
  have hcoc : lift (vectorPoint e x) (vectorPoint e x') ≫ N.cocycle =
      vectorPoint e' (N.cocycleCoordinates e e' x x') := by
    rw [cocycleCoordinates, vectorPoint_toAdd]
  rw [hcoc, ← vectorPoint_add] at hsec
  calc (vectorPoint e' w ≫ N.inclusion.hom.hom) * (vectorPoint e x ≫ N.sec) *
        ((vectorPoint e' w' ≫ N.inclusion.hom.hom) * (vectorPoint e x' ≫ N.sec))
      = (vectorPoint e' w ≫ N.inclusion.hom.hom) * (vectorPoint e' w' ≫ N.inclusion.hom.hom) *
          ((vectorPoint e x ≫ N.sec) * (vectorPoint e x' ≫ N.sec)) := by
        rw [mul_assoc, ← mul_assoc (vectorPoint e x ≫ N.sec), ← hc.eq]
        group
    _ = _ := by
        rw [hsec, ← mul_assoc, ← MonObj.mul_comp, ← MonObj.mul_comp, ← vectorPoint_add,
          ← vectorPoint_add]

theorem act_chartPoint
    (he : IsWeightVectorCoordinates C.action a e)
    (he' : IsWeightVectorCoordinates (subgroupAction i (2 • a) j₂ hj₂) (2 • a) e')
    (t : rationalPoints S.toGrp) (x : Fin d → K) (w : Fin m → K) :
    (subgroupAction i a j hj).act t (N.chartPoint e e' x w) =
      N.chartPoint e e'
        ((rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm a) t : K) • x)
        ((rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm a) t : K) ^ 2
          • w) := by
  rw [chartPoint_def, chartPoint_def, AutomorphicAction.act_mul_right, N.act_inclusion,
    N.act_sec, act_vectorPoint e he, act_vectorPoint e' he', rationalCharacterEval_two_nsmul,
    Units.val_pow_eq_pow_val]

/-- The cocycle in `K`-valued coordinates is `K`-bilinear. -/
def cocycleForm (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (he : IsWeightVectorCoordinates C.action a e)
    (he' : IsWeightVectorCoordinates (subgroupAction i (2 • a) j₂ hj₂) (2 • a) e') :
    (Fin d → K) →ₗ[K] (Fin d → K) →ₗ[K] (Fin m → K) :=
  have hb := N.isBilinearVectorPairing_cocycle hS ha he he'
  LinearMap.mk₂ K (N.cocycleCoordinates e e')
    (fun x x' y => by
      have h := (hb (Over.mk (𝟙 _)) (vectorPoint e x) (vectorPoint e x') (vectorPoint e y)
        (vectorPoint e y) 0).1
      rw [← vectorPoint_add] at h
      simp only [cocycleCoordinates, toAdd_rationalVectorCoordinates, h]
      funext l
      simp only [Pi.add_apply, map_add])
    (fun c x y => by
      have h := (hb (Over.mk (𝟙 _)) (vectorPoint e x) (vectorPoint e x) (vectorPoint e y)
        (vectorPoint e y)
        ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm c)).2.2.1
      rw [← vectorPoint_smul] at h
      simp only [cocycleCoordinates, toAdd_rationalVectorCoordinates, h]
      funext l
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply])
    (fun x y y' => by
      have h := (hb (Over.mk (𝟙 _)) (vectorPoint e x) (vectorPoint e x) (vectorPoint e y)
        (vectorPoint e y') 0).2.1
      rw [← vectorPoint_add] at h
      simp only [cocycleCoordinates, toAdd_rationalVectorCoordinates, h]
      funext l
      simp only [Pi.add_apply, map_add])
    (fun c x y => by
      have h := (hb (Over.mk (𝟙 _)) (vectorPoint e x) (vectorPoint e x) (vectorPoint e y)
        (vectorPoint e y)
        ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm c)).2.2.2
      rw [← vectorPoint_smul] at h
      simp only [cocycleCoordinates, toAdd_rationalVectorCoordinates, h]
      funext l
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply])

theorem cocycleForm_apply (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (he : IsWeightVectorCoordinates C.action a e)
    (he' : IsWeightVectorCoordinates (subgroupAction i (2 • a) j₂ hj₂) (2 • a) e')
    (x y : Fin d → K) :
    N.cocycleForm e e' hS ha he he' x y = N.cocycleCoordinates e e' x y :=
  rfl

/-- The quotient coordinates of a rational point of the root group in the chart
`g = incl(w) * sec(x)`. -/
def chartFirst (g : rationalPoints U) : Fin d → K :=
  Classical.choose (N.exists_eq_chartPoint e e' g)

/-- The doubled-root coordinates of a rational point of the root group in the chart
`g = incl(w) * sec(x)`. -/
def chartSecond (g : rationalPoints U) : Fin m → K :=
  Classical.choose (Classical.choose_spec (N.exists_eq_chartPoint e e' g))

theorem eq_chartPoint (g : rationalPoints U) :
    g = N.chartPoint e e' (N.chartFirst e e' g) (N.chartSecond e e' g) :=
  Classical.choose_spec (Classical.choose_spec (N.exists_eq_chartPoint e e' g))

@[simp] theorem chartFirst_chartPoint (x : Fin d → K) (w : Fin m → K) :
    N.chartFirst e e' (N.chartPoint e e' x w) = x :=
  (N.chartPoint_injective e e' (N.eq_chartPoint e e' (N.chartPoint e e' x w)).symm).1

@[simp] theorem chartSecond_chartPoint (x : Fin d → K) (w : Fin m → K) :
    N.chartSecond e e' (N.chartPoint e e' x w) = w :=
  (N.chartPoint_injective e e' (N.eq_chartPoint e e' (N.chartPoint e e' x w)).symm).2

theorem chartPoint_inj {x x' : Fin d → K} {w w' : Fin m → K} :
    N.chartPoint e e' x w = N.chartPoint e e' x' w' ↔ x = x' ∧ w = w' :=
  ⟨N.chartPoint_injective e e', fun h => by rw [h.1, h.2]⟩

theorem comp_quotient_eq (g : rationalPoints U) :
    g ≫ C.q.hom.hom = vectorPoint e (N.chartFirst e e' g) := by
  obtain ⟨x, w, rfl⟩ := N.exists_eq_chartPoint e e' g
  rw [chartFirst_chartPoint, chartPoint_comp_quotient]

theorem chartFirst_eq_zero_iff (g : rationalPoints U) :
    N.chartFirst e e' g = 0 ↔ g ≫ C.q.hom.hom = 1 := by
  rw [N.comp_quotient_eq e e', vectorPoint_eq_one_iff]

@[simp] theorem chartFirst_one : N.chartFirst e e' 1 = 0 := by
  rw [← N.chartPoint_zero_zero e e', chartFirst_chartPoint]

@[simp] theorem chartSecond_one : N.chartSecond e e' 1 = 0 := by
  rw [← N.chartPoint_zero_zero e e', chartSecond_chartPoint]

theorem chartFirst_mul [IsAffineHom G.X.hom] [Smooth G.X.hom] (hS : IsSplitTorus S.toGrp)
    (ha : a ≠ 0) (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i)
    (g h : rationalPoints U) :
    N.chartFirst e e' (g * h) = N.chartFirst e e' g + N.chartFirst e e' h := by
  obtain ⟨x, w, rfl⟩ := N.exists_eq_chartPoint e e' g
  obtain ⟨x', w', rfl⟩ := N.exists_eq_chartPoint e e' h
  rw [N.chartPoint_mul e e' hS ha hhigh]
  simp only [chartFirst_chartPoint]

theorem chartSecond_mul [IsAffineHom G.X.hom] [Smooth G.X.hom] (hS : IsSplitTorus S.toGrp)
    (ha : a ≠ 0) (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i)
    (g h : rationalPoints U) :
    N.chartSecond e e' (g * h) = N.chartSecond e e' g + N.chartSecond e e' h +
      N.cocycleCoordinates e e' (N.chartFirst e e' g) (N.chartFirst e e' h) := by
  obtain ⟨x, w, rfl⟩ := N.exists_eq_chartPoint e e' g
  obtain ⟨x', w', rfl⟩ := N.exists_eq_chartPoint e e' h
  rw [N.chartPoint_mul e e' hS ha hhigh]
  simp only [chartFirst_chartPoint, chartSecond_chartPoint]

theorem chartFirst_act (he : IsWeightVectorCoordinates C.action a e)
    (he' : IsWeightVectorCoordinates (subgroupAction i (2 • a) j₂ hj₂) (2 • a) e')
    (t : rationalPoints S.toGrp) (g : rationalPoints U) :
    N.chartFirst e e' ((subgroupAction i a j hj).act t g) =
      (rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm a) t : K) •
        N.chartFirst e e' g := by
  obtain ⟨x, w, rfl⟩ := N.exists_eq_chartPoint e e' g
  rw [N.act_chartPoint e e' he he', chartFirst_chartPoint, chartFirst_chartPoint]

theorem chartSecond_act (he : IsWeightVectorCoordinates C.action a e)
    (he' : IsWeightVectorCoordinates (subgroupAction i (2 • a) j₂ hj₂) (2 • a) e')
    (t : rationalPoints S.toGrp) (g : rationalPoints U) :
    N.chartSecond e e' ((subgroupAction i a j hj).act t g) =
      (rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm a) t : K) ^ 2 •
        N.chartSecond e e' g := by
  obtain ⟨x, w, rfl⟩ := N.exists_eq_chartPoint e e' g
  rw [N.act_chartPoint e e' he he', chartSecond_chartPoint, chartSecond_chartPoint]

/-- **Chart form of unitary coordinates.** A bijective homomorphism `φ` from the rational
unitary parameters of `L / E` (with `K ⊆ E`) to the rational points of the root group, which
sends exactly the central parameters into the doubled root group and intertwines the scaling
by every `c ∈ Kˣ` with the action of a torus point whose root value is `c`, has the chart form
`φ(u, v) = incl(B v + H(u, u)) * sec(A u)`, with `A` a `K`-linear bijection, `B` `K`-linear
and bijective on the trace-zero elements, and `H` `K`-bilinear. -/
theorem exists_unitaryChartForm [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i)
    (he : IsWeightVectorCoordinates C.action a e)
    (he' : IsWeightVectorCoordinates (subgroupAction i (2 • a) j₂ hj₂) (2 • a) e')
    {E L : Type*} [Field E] [Field L] [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L] [Algebra.IsQuadraticExtension E L] [Algebra.IsSeparable E L]
    [FiniteDimensional K L]
    (φ : SU3Root.rationalParameters E L →* rationalPoints U)
    (hinj : Function.Injective φ) (hsurj : Function.Surjective φ)
    (hcentral : ∀ p : SU3Root.rationalParameters E L, φ p ≫ C.q.hom.hom = 1 ↔ p.first = 0)
    (hscale : ∀ c : K, c ≠ 0 → ∃ t : rationalPoints S.toGrp,
      (rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm a) t : K) = c ∧
      ∀ p, (subgroupAction i a j hj).act t (φ p) =
        φ (SU3Root.Parameters.scale (algebraMap K L c) p)) :
    ∃ (A : L →ₗ[K] (Fin d → K)) (B : L →ₗ[K] (Fin m → K))
      (H : L →ₗ[K] L →ₗ[K] (Fin m → K)),
      Function.Bijective A ∧
      (∀ w : Fin m → K, ∃! z : L, z + SU3Root.conjugation E L z = 0 ∧ B z = w) ∧
      ∀ p, φ p = N.chartPoint e e' (A p.first) (B p.second + H p.first p.first) := by
  classical
  set β := N.cocycleForm e e' hS ha he he' with hβ
  obtain ⟨X, hX⟩ : ∃ X : SU3Root.rationalParameters E L → (Fin d → K),
      ∀ p, X p = N.chartFirst e e' (φ p) := ⟨_, fun _ => rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : SU3Root.rationalParameters E L → (Fin m → K),
      ∀ p, W p = N.chartSecond e e' (φ p) := ⟨_, fun _ => rfl⟩
  have hφ : ∀ p, φ p = N.chartPoint e e' (X p) (W p) := fun p => by
    rw [hX, hW]
    exact N.eq_chartPoint e e' (φ p)
  have hXmul : ∀ p q, X (p * q) = X p + X q := fun p q => by
    simp only [hX, map_mul, N.chartFirst_mul e e' hS ha hhigh]
  have hWmul : ∀ p q, W (p * q) = W p + W q + β (X p) (X q) := fun p q => by
    simp only [hX, hW, map_mul, N.chartSecond_mul e e' hS ha hhigh, hβ, cocycleForm_apply]
  have hX1 : X 1 = 0 := by rw [hX, map_one, chartFirst_one]
  have hW1 : W 1 = 0 := by rw [hW, map_one, chartSecond_one]
  have hX0 : ∀ p, X p = 0 ↔ p.first = 0 := fun p => by
    rw [hX, chartFirst_eq_zero_iff, hcentral]
  have hβ0 : ∀ x, β x 0 = 0 := fun x => map_zero _
  have hconjK : ∀ c : K, SU3Root.conjugation E L (algebraMap K L c) = algebraMap K L c :=
    fun c => by rw [IsScalarTower.algebraMap_apply K E L, AlgEquiv.commutes]
  have hscale0 : ∀ p : SU3Root.rationalParameters E L,
      SU3Root.Parameters.scale (algebraMap K L 0) p = 1 := fun p => by
    ext <;> simp
  have hscaleX : ∀ (c : K) p, X (SU3Root.Parameters.scale (algebraMap K L c) p) = c • X p := by
    intro c p
    by_cases hc : c = 0
    · subst hc
      rw [hscale0, hX1, zero_smul]
    · obtain ⟨t, ht, hact⟩ := hscale c hc
      rw [hX, hX, ← hact, N.chartFirst_act e e' he he', ht]
  have hscaleW : ∀ (c : K) p,
      W (SU3Root.Parameters.scale (algebraMap K L c) p) = (c * c) • W p := by
    intro c p
    by_cases hc : c = 0
    · subst hc
      rw [hscale0, hW1, mul_zero, zero_smul]
    · obtain ⟨t, ht, hact⟩ := hscale c hc
      rw [hW, hW, ← hact, N.chartSecond_act e e' he he', ht, sq]
  have hXfirst : ∀ p q : SU3Root.rationalParameters E L, p.first = q.first → X p = X q := by
    intro p q hpq
    have h : X q = X p + X (p⁻¹ * q) := by rw [← hXmul, mul_inv_cancel_left]
    rw [h, (hX0 (p⁻¹ * q)).2 (by simp [hpq]), add_zero]
  -- The linear map `A` on first coordinates.
  obtain ⟨A, hA⟩ : ∃ A : L →ₗ[K] (Fin d → K), ∀ p, A p.first = X p :=
    ⟨{ toFun := fun u => X (SU3Root.rationalLift E L u)
       map_add' := fun u v => by
         rw [← hXmul]
         exact hXfirst _ _ (by simp)
       map_smul' := fun c u => by
         rw [RingHom.id_apply, ← hscaleX]
         exact hXfirst _ _ (by simp [Algebra.smul_def]) },
     fun p => hXfirst _ _ (SU3Root.rationalLift_first E L _)⟩
  have hAl : ∀ u, A u = X (SU3Root.rationalLift E L u) := fun u =>
    hA (SU3Root.rationalLift E L u)
  -- The linear map `B` on trace-zero second coordinates, from the commutator with `lift 1`.
  obtain ⟨B, hB⟩ : ∃ B : L →ₗ[K] (Fin m → K), ∀ z,
      B z = β (A (SU3Root.traceOne E L * z)) (A 1) - β (A 1) (A (SU3Root.traceOne E L * z)) :=
    ⟨((β.comp A).flip (A 1) - (β (A 1)).comp A).comp
      (LinearMap.mulLeft K (SU3Root.traceOne E L)), fun z => by simp⟩
  have hκ := SU3Root.traceOne_add_conjugate E L
  have hWcentral : ∀ p : SU3Root.rationalParameters E L, p.first = 0 → W p = B p.second := by
    intro p hp
    have hz : p.second + SU3Root.conjugation E L p.second = 0 := by
      have := p.equation
      rw [hp] at this
      simpa using this
    have hprod : SU3Root.rationalLift E L (SU3Root.traceOne E L * p.second) *
        SU3Root.rationalLift E L 1 =
        SU3Root.rationalLift E L 1 *
          SU3Root.rationalLift E L (SU3Root.traceOne E L * p.second) * p := by
      ext
      · simp [hp, add_comm]
      · simp only [SU3Root.Parameters.second_mul, SU3Root.Parameters.first_mul,
          SU3Root.rationalLift_first, SU3Root.fieldInvolution_bar, hp, map_one, map_mul,
          map_zero, mul_zero, add_zero, mul_one, one_mul]
        linear_combination (-(SU3Root.conjugation E L (SU3Root.traceOne E L))) * hz +
          p.second * hκ
    have h := congrArg W hprod
    rw [hWmul, hWmul, hWmul, (hX0 p).2 hp, hβ0, add_zero, ← hAl, ← hAl] at h
    rw [hB]
    linear_combination -h
  -- The general formula `W p = B p.second + Q p.first`.
  obtain ⟨Q, hQ⟩ : ∃ Q : L → (Fin m → K),
      ∀ u, Q u = W (SU3Root.rationalLift E L u) - B (SU3Root.rationalLift E L u).second :=
    ⟨_, fun _ => rfl⟩
  have hWQ : ∀ p, W p = B p.second + Q p.first := by
    intro p
    have h1 : p = SU3Root.rationalLift E L p.first * ((SU3Root.rationalLift E L p.first)⁻¹ * p) :=
      (mul_inv_cancel_left _ _).symm
    have hfirst : ((SU3Root.rationalLift E L p.first)⁻¹ * p).first = 0 := by simp
    have hsecond : ((SU3Root.rationalLift E L p.first)⁻¹ * p).second =
        p.second - (SU3Root.rationalLift E L p.first).second := by
      have := (SU3Root.rationalLift E L p.first).equation
      simp only [SU3Root.Parameters.second_mul, SU3Root.Parameters.second_inv,
        SU3Root.Parameters.first_inv, SU3Root.rationalLift_first] at this ⊢
      linear_combination this
    conv_lhs => rw [h1]
    rw [hWmul, (hX0 _).2 hfirst, hβ0, add_zero, hWcentral _ hfirst, hsecond, map_sub, hQ]
    abel
  -- `Q` is a quadratic map.
  have hQsmul : ∀ (c : K) u, Q (c • u) = (c * c) • Q u := by
    intro c u
    have h := hscaleW c (SU3Root.rationalLift E L u)
    have hs : (SU3Root.Parameters.scale (algebraMap K L c) (SU3Root.rationalLift E L u)).second =
        (c * c) • (SU3Root.rationalLift E L u).second := by
      rw [SU3Root.Parameters.second_scale, SU3Root.fieldInvolution_bar, hconjK, ← map_mul,
        ← Algebra.smul_def]
    have hf : (SU3Root.Parameters.scale (algebraMap K L c) (SU3Root.rationalLift E L u)).first =
        c • u := by
      rw [SU3Root.Parameters.first_scale, SU3Root.rationalLift_first, ← Algebra.smul_def]
    rw [hWQ, hWQ (SU3Root.rationalLift E L u), hs, hf, map_smul, SU3Root.rationalLift_first,
      smul_add] at h
    exact add_left_cancel h
  have hQadd : ∀ u v, Q (u + v) =
      Q u + Q v + (β (A u) (A v) - B (u * SU3Root.conjugation E L v)) := by
    intro u v
    have h := hWmul (SU3Root.rationalLift E L u) (SU3Root.rationalLift E L v)
    rw [hWQ, hWQ (SU3Root.rationalLift E L u), hWQ (SU3Root.rationalLift E L v), ← hAl,
      ← hAl] at h
    simp only [SU3Root.Parameters.second_mul, SU3Root.Parameters.first_mul,
      SU3Root.rationalLift_first, SU3Root.fieldInvolution_bar, map_add] at h
    linear_combination h
  let σK : L →ₗ[K] L := ((SU3Root.conjugation E L).restrictScalars K).toLinearMap
  let Qm : QuadraticMap K L (Fin m → K) :=
    { toFun := Q
      toFun_smul := hQsmul
      exists_companion' := ⟨β.compl₁₂ A A - ((LinearMap.mul K L).compl₂ σK).compr₂ B,
        fun u v => by
          rw [hQadd]
          simp [σK]⟩ }
  set H := Qm.toBilin (Module.finBasis K L) with hHdef
  have hH : ∀ u, H u u = Q u := fun u => by
    have := congrArg (fun F : QuadraticMap K L (Fin m → K) => F u)
      (QuadraticMap.toQuadraticMap_toBilin Qm (Module.finBasis K L))
    simpa [Qm] using this
  have hform : ∀ p, φ p = N.chartPoint e e' (A p.first) (B p.second + H p.first p.first) := by
    intro p
    rw [hφ p, hA, hH, ← hWQ]
  have hAinj : Function.Injective A := by
    refine (injective_iff_map_eq_zero A).2 fun u hu => ?_
    rw [hAl, hX0] at hu
    simpa using hu
  have hAsurj : Function.Surjective A := by
    intro x
    obtain ⟨p, hp⟩ := hsurj (N.chartPoint e e' x 0)
    refine ⟨p.first, ?_⟩
    rw [hA, hX, hp, chartFirst_chartPoint]
  refine ⟨A, B, H, ⟨hAinj, hAsurj⟩, fun w => ?_, hform⟩
  obtain ⟨p, hp⟩ := hsurj (N.chartPoint e e' 0 w)
  have hp' := hp
  rw [hform p, chartPoint_inj] at hp'
  have hp1 : p.first = 0 := by
    apply hAinj
    rw [hp'.1, map_zero]
  refine ⟨p.second, ⟨?_, ?_⟩, ?_⟩
  · have := p.equation
    rw [hp1] at this
    simpa using this
  · rw [← hp'.2, hp1]
    simp
  · rintro z ⟨hz, hBz⟩
    let q : SU3Root.rationalParameters E L := ⟨(0, z), by simp [hz]⟩
    have hq : φ q = φ p := by
      rw [hp, hform q]
      change N.chartPoint e e' (A 0) (B z + H 0 0) = _
      rw [hBz]
      simp
    exact congrArg SU3Root.Parameters.second (hinj hq)

end HeisenbergNormalForm

end Chart

end Langlands.GroupScheme.RelativeRoot
