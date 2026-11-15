import Langlands.Geometry.Building.RootUnitaryHeisenbergAssembly

/-! # Heisenberg chart points of a multipliable root group on every test scheme

For a Heisenberg normal form of a multipliable relative root group `U = U_a`, with vector
coordinates `e` on the quotient `V = U / U_{2a}` and `e'` on `U₂ = U_{2a}`, every point of `U`
over every test scheme is uniquely `incl(w) · sec(x)` for coordinate vectors `w` and `x`. In
these coordinates the group law is `(w, x) (w', x') = (w + w' + β(x, x'), x + x')` with `β`
the cocycle written in coordinates. The rational chart points, with `K`-valued coordinates,
are the chart points over the identity test scheme.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section Rational

variable {K : Type u} [Field K]

/-- `K`-valued coordinates on the rational points of a group scheme with vector coordinates:
the coordinates on the identity test scheme, read through `Γ(Spec K, 𝒪) ≅ K`. -/
def rationalVectorCoordinates {V : GroupScheme (Spec (CommRingCat.of K))} {n : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of K)),
      (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤))) :
    rationalPoints V ≃* Multiplicative (Fin n → K) :=
  (e (Over.mk (𝟙 _))).trans (AddEquiv.toMultiplicative (AddEquiv.piCongrRight fun _ =>
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toAddEquiv))

variable {S : CommGroupScheme (Spec (CommRingCat.of K))}
    {G U U₂ : GroupScheme (Spec (CommRingCat.of K))}
    {i : S.toGrp ⟶ G} {a : characterLattice S}
    {j : U ⟶ G} {hj : (subgroup i a).IsRepresentedBy j}
    {j₂ : U₂ ⟶ G} {hj₂ : (subgroup i (2 • a)).IsRepresentedBy j₂}
    {C : DoubleRootCommutatorPairing i a hj hj₂}

/-- The rational chart point `incl(w) * sec(x)` of a Heisenberg normal form, for `K`-valued
coordinates `x` on the quotient and `w` on the doubled root group. -/
def HeisenbergNormalForm.chartPoint (N : HeisenbergNormalForm C) {d m : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of K)),
      (T ⟶ C.V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (e' : ∀ T : Over (Spec (CommRingCat.of K)),
      (T ⟶ U₂.X) ≃* Multiplicative (Fin m → Γ(T.left, ⊤)))
    (x : Fin d → K) (w : Fin m → K) : rationalPoints U :=
  ((rationalVectorCoordinates e').symm (Multiplicative.ofAdd w) ≫ N.inclusion.hom.hom) *
    ((rationalVectorCoordinates e).symm (Multiplicative.ofAdd x) ≫ N.sec)

end Rational

end Langlands.GroupScheme.RelativeRoot

namespace Langlands.GroupScheme.RelativeRoot.HeisenbergNormalForm

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G U U₂ : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} {a : characterLattice S}
    {j : U ⟶ G} {hj : (subgroup i a).IsRepresentedBy j}
    {j₂ : U₂ ⟶ G} {hj₂ : (subgroup i (2 • a)).IsRepresentedBy j₂}
    {C : DoubleRootCommutatorPairing i a hj hj₂} (N : HeisenbergNormalForm C) {d m : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ C.V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (e' : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ U₂.X) ≃* Multiplicative (Fin m → Γ(T.left, ⊤)))

/-- The point `incl(w) · sec(x)` of the root group with Heisenberg coordinates `(w, x)` over a
test scheme `T`. -/
def testChartPoint (T : Over (Spec (CommRingCat.of k))) (w : Fin m → Γ(T.left, ⊤))
    (x : Fin d → Γ(T.left, ⊤)) : T ⟶ U.X :=
  ((e' T).symm (Multiplicative.ofAdd w) ≫ N.inclusion.hom.hom) *
    ((e T).symm (Multiplicative.ofAdd x) ≫ N.sec)

/-- The cocycle of the normal form, written in the coordinates `e` and `e'`. -/
def chartCocycle (T : Over (Spec (CommRingCat.of k))) (x y : Fin d → Γ(T.left, ⊤)) :
    Fin m → Γ(T.left, ⊤) :=
  (e' T (lift ((e T).symm (Multiplicative.ofAdd x)) ((e T).symm (Multiplicative.ofAdd y)) ≫
    N.cocycle)).toAdd

theorem testChartPoint_comp_q (T : Over (Spec (CommRingCat.of k))) (w : Fin m → Γ(T.left, ⊤))
    (x : Fin d → Γ(T.left, ⊤)) :
    N.testChartPoint e e' T w x ≫ C.q.hom.hom = (e T).symm (Multiplicative.ofAdd x) := by
  rw [testChartPoint, MonObj.mul_comp, Geometry.Building.HeisenbergUnitaryData.inclusion_comp_q N, Category.assoc,
    N.sec_comp, Category.comp_id, one_mul]

/-- **The Heisenberg law** of chart points. -/
theorem testChartPoint_mul (T : Over (Spec (CommRingCat.of k))) (w w' : Fin m → Γ(T.left, ⊤))
    (x x' : Fin d → Γ(T.left, ⊤)) :
    N.testChartPoint e e' T w x * N.testChartPoint e e' T w' x' =
      N.testChartPoint e e' T (w + w' + N.chartCocycle e e' T x x') (x + x') := by
  have hcomm : Commute ((e T).symm (Multiplicative.ofAdd x) ≫ N.sec)
      ((e' T).symm (Multiplicative.ofAdd w') ≫ N.inclusion.hom.hom) :=
    Geometry.Building.commute_of_comp_q C _ _ (Geometry.Building.HeisenbergUnitaryData.inclusion_comp_q N _)
  have hsec := N.sec_mul T ((e T).symm (Multiplicative.ofAdd x))
    ((e T).symm (Multiplicative.ofAdd x'))
  have hβ : lift ((e T).symm (Multiplicative.ofAdd x)) ((e T).symm (Multiplicative.ofAdd x')) ≫
      N.cocycle = (e' T).symm (Multiplicative.ofAdd (N.chartCocycle e e' T x x')) := by
    rw [chartCocycle, ofAdd_toAdd, MulEquiv.symm_apply_apply]
  rw [hβ] at hsec
  simp only [testChartPoint, ofAdd_add, map_mul, MonObj.mul_comp]
  calc ((e' T).symm (Multiplicative.ofAdd w) ≫ N.inclusion.hom.hom) *
        ((e T).symm (Multiplicative.ofAdd x) ≫ N.sec) *
        (((e' T).symm (Multiplicative.ofAdd w') ≫ N.inclusion.hom.hom) *
          ((e T).symm (Multiplicative.ofAdd x') ≫ N.sec))
      = ((e' T).symm (Multiplicative.ofAdd w) ≫ N.inclusion.hom.hom) *
          (((e T).symm (Multiplicative.ofAdd x) ≫ N.sec) *
            ((e' T).symm (Multiplicative.ofAdd w') ≫ N.inclusion.hom.hom)) *
          ((e T).symm (Multiplicative.ofAdd x') ≫ N.sec) := by group
    _ = ((e' T).symm (Multiplicative.ofAdd w) ≫ N.inclusion.hom.hom) *
          (((e' T).symm (Multiplicative.ofAdd w') ≫ N.inclusion.hom.hom) *
            ((e T).symm (Multiplicative.ofAdd x) ≫ N.sec)) *
          ((e T).symm (Multiplicative.ofAdd x') ≫ N.sec) := by rw [hcomm.eq]
    _ = ((e' T).symm (Multiplicative.ofAdd w) ≫ N.inclusion.hom.hom) *
          ((e' T).symm (Multiplicative.ofAdd w') ≫ N.inclusion.hom.hom) *
          (((e T).symm (Multiplicative.ofAdd x) ≫ N.sec) *
            ((e T).symm (Multiplicative.ofAdd x') ≫ N.sec)) := by group
    _ = _ := by rw [hsec]; group

/-- Chart points determine their coordinates. -/
theorem testChartPoint_injective {T : Over (Spec (CommRingCat.of k))}
    {w w' : Fin m → Γ(T.left, ⊤)} {x x' : Fin d → Γ(T.left, ⊤)}
    (h : N.testChartPoint e e' T w x = N.testChartPoint e e' T w' x') : w = w' ∧ x = x' := by
  have hx : x = x' := by
    have h1 := congrArg (· ≫ C.q.hom.hom) h
    simp only [testChartPoint_comp_q] at h1
    exact Multiplicative.ofAdd.injective ((e T).symm.injective h1)
  subst hx
  refine ⟨?_, rfl⟩
  have h2 : (e' T).symm (Multiplicative.ofAdd w) ≫ N.inclusion.hom.hom =
      (e' T).symm (Multiplicative.ofAdd w') ≫ N.inclusion.hom.hom := mul_right_cancel h
  let := N.mono_inclusion
  exact Multiplicative.ofAdd.injective ((e' T).symm.injective ((cancel_mono _).1 h2))

/-- Every point of the root group is a chart point. -/
theorem exists_testChartPoint_eq {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ U.X) :
    ∃ w x, N.testChartPoint e e' T w x = g := by
  obtain ⟨w₀, hw₀⟩ := N.exists_eq_mul_sec g
  refine ⟨Multiplicative.toAdd (e' T w₀), Multiplicative.toAdd (e T (g ≫ C.q.hom.hom)), ?_⟩
  simp only [testChartPoint, ofAdd_toAdd, MulEquiv.symm_apply_apply]
  exact hw₀.symm

/-- The rational chart points are the chart points over the identity test scheme, with the
coordinates read through `K ≅ Γ(Spec K, 𝒪)`. -/
theorem chartPoint_eq_testChartPoint (x : Fin d → k) (w : Fin m → k) :
    N.chartPoint e e' x w =
      N.testChartPoint e e' (Over.mk (𝟙 _)) (fun l => (Scheme.ΓSpecIso (CommRingCat.of k)).inv (w l))
        (fun l => (Scheme.ΓSpecIso (CommRingCat.of k)).inv (x l)) :=
  rfl

variable {e e'}

theorem comp_symm_ofAdd_of_isNatural {n : ℕ} {V : GroupScheme (Spec (CommRingCat.of k))}
    {c : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤))}
    (hc : IsNaturalVectorCoordinates c) {T T' : Over (Spec (CommRingCat.of k))}
    (f : T' ⟶ T) (x : Fin n → Γ(T.left, ⊤)) :
    f ≫ (c T).symm (Multiplicative.ofAdd x) =
      (c T').symm (Multiplicative.ofAdd fun l => f.left.appTop (x l)) := by
  apply (c T').injective
  apply Multiplicative.toAdd.injective
  rw [hc T T' f, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  rfl

/-- Chart points are natural in the test scheme. -/
theorem comp_testChartPoint (he : IsNaturalVectorCoordinates e) (he' : IsNaturalVectorCoordinates e')
    {T T' : Over (Spec (CommRingCat.of k))} (f : T' ⟶ T) (w : Fin m → Γ(T.left, ⊤))
    (x : Fin d → Γ(T.left, ⊤)) :
    f ≫ N.testChartPoint e e' T w x =
      N.testChartPoint e e' T' (fun l => f.left.appTop (w l)) (fun l => f.left.appTop (x l)) := by
  rw [testChartPoint, testChartPoint, MonObj.comp_mul, ← Category.assoc, ← Category.assoc,
    comp_symm_ofAdd_of_isNatural he' f, comp_symm_ofAdd_of_isNatural he f]

/-- The coordinate cocycle is the published coordinate pairing of the cocycle over the
relative global sections. -/
theorem chartCocycle_eq_coordinatePairing (he : IsNaturalVectorCoordinates e)
    (he' : IsNaturalVectorCoordinates e') (T : Over (Spec (CommRingCat.of k)))
    (x y : Fin d → Γ(T.left, ⊤)) :
    N.chartCocycle e e' T x y =
      coordinatePairing (A := ((algΓ (CommRingCat.of k)).obj T).unop) e e' N.cocycle x y := by
  rw [chartCocycle, coordinatePairing_global he he', MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply, toAdd_ofAdd, toAdd_ofAdd]

end Langlands.GroupScheme.RelativeRoot.HeisenbergNormalForm
