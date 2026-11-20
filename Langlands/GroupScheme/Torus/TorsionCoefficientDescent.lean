import Langlands.GroupScheme.Torus.TorsionDensityLattice

/-! # Coefficient descent detected on the torsion of a split torus -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.TorsionDensity

variable (L : Type v) [Fintype L]

/-- On the character algebra of a split torus, restriction to `n`-torsion
sends an exponent to its class modulo `n` times the lattice. -/
def torsionCoefficientMap (R : Type u) [CommSemiring R] (n : ℕ) :
    AddMonoidAlgebra R (L → ℤ) →+*
      AddMonoidAlgebra R ((L → ℤ) ⧸ multiples (L → ℤ) n) :=
  AddMonoidAlgebra.mapDomainRingHom R (QuotientAddGroup.mk' (multiples _ n))

private theorem exists_bound_injOn_free (s : Finset (L → ℤ)) :
    ∃ M : ℕ, ∀ n : ℕ, M < n →
      Set.InjOn (QuotientAddGroup.mk' (multiples (L → ℤ) n)) (s : Set (L → ℤ)) := by
  let forgetUnit : (L → ℤ) × PUnit ≃+ (L → ℤ) := AddEquiv.prodUnique
  let e := forgetUnit.symm
  obtain ⟨M, hM⟩ := exists_bound_injOn e s
  exact ⟨M, fun n hn => hM n (by simp) hn⟩

variable {R K : Type u} [CommRing R] [CommRing K] (φ : R →+* K)

/-- Coefficients of a Laurent polynomial descend if its torsion
restrictions descend for an unbounded set of orders. -/
theorem exists_preimage_of_torsionCoefficientMap
    (x : AddMonoidAlgebra K (L → ℤ))
    (P : ℕ → Prop) (hP : ∀ M : ℕ, ∃ n, P n ∧ M < n)
    (h : ∀ n, P n →
      torsionCoefficientMap L K n x ∈
        Set.range (AddMonoidAlgebra.mapRingHom ((L → ℤ) ⧸ multiples (L → ℤ) n) φ)) :
    x ∈ Set.range (AddMonoidAlgebra.mapRingHom (L → ℤ) φ) := by
  classical
  obtain ⟨M, hM⟩ := exists_bound_injOn_free L x.coeff.support
  obtain ⟨n, hn, hMn⟩ := hP M
  obtain ⟨y, hy⟩ := h n hn
  let q := QuotientAddGroup.mk' (multiples (L → ℤ) n)
  let c : (L → ℤ) → R := fun a => if a ∈ x.coeff.support then y.coeff (q a) else 0
  have hc (a : L → ℤ) (ha : c a ≠ 0) : a ∈ x.coeff.support := by
    by_contra hNot
    exact ha (ite_eq_right hNot)
  use AddMonoidAlgebra.ofCoeff (Finsupp.onFinset x.coeff.support c hc)
  apply AddMonoidAlgebra.coeff_injective
  ext a
  rw [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.coeff_ofCoeff,
    Finsupp.onFinset_apply]
  by_cases ha : a ∈ x.coeff.support
  · change φ (if a ∈ x.coeff.support then y.coeff (q a) else 0) = x.coeff a
    rw [ite_eq_left ha]
    have hCoeff := congrArg (fun z : AddMonoidAlgebra K _ => z.coeff (q a)) hy
    rw [AddMonoidAlgebra.coeff_mapRingHom] at hCoeff
    change φ (y.coeff (q a)) = Finsupp.mapDomain q x.coeff (q a) at hCoeff
    exact hCoeff.trans (Finsupp.mapDomain_apply' _ x.coeff subset_rfl (hM n hMn) ha)
  · change φ (if a ∈ x.coeff.support then y.coeff (q a) else 0) = x.coeff a
    rw [ite_eq_right ha, map_zero, Finsupp.notMem_support_iff.mp ha]

variable {C : Type u} [CommRing C]

/-- A ring map to the character algebra over an extension ring descends
uniquely along an injective coefficient map when its torsion restrictions
already descend for unbounded orders. -/
theorem existsUnique_ringHom_of_torsionCoefficientMap (hφ : Function.Injective φ)
    (f : C →+* AddMonoidAlgebra K (L → ℤ))
    (P : ℕ → Prop) (hP : ∀ M : ℕ, ∃ n, P n ∧ M < n)
    (h : ∀ n, P n →
      ∃ g : C →+* AddMonoidAlgebra R ((L → ℤ) ⧸ multiples (L → ℤ) n),
        (AddMonoidAlgebra.mapRingHom _ φ).comp g = (torsionCoefficientMap L K n).comp f) :
    ∃! g : C →+* AddMonoidAlgebra R (L → ℤ),
      (AddMonoidAlgebra.mapRingHom _ φ).comp g = f := by
  let i := AddMonoidAlgebra.mapRingHom (L → ℤ) φ
  have hi : Function.Injective i := AddMonoidAlgebra.map_injective _ hφ
  have hex (x : C) : ∃ y, i y = f x := by
    apply exists_preimage_of_torsionCoefficientMap L φ (f x) P hP
    intro n hn
    obtain ⟨g, hg⟩ := h n hn
    exact ⟨g x, congrFun (congrArg DFunLike.coe hg) x⟩
  choose g hg using hex
  let gHom : C →+* AddMonoidAlgebra R (L → ℤ) :=
    { toFun := g
      map_zero' := hi (by rw [hg, map_zero, map_zero])
      map_one' := hi (by rw [hg, map_one, map_one])
      map_add' := fun x y => hi (by rw [map_add, hg, hg, hg, map_add])
      map_mul' := fun x y => hi (by rw [map_mul, hg, hg, hg, map_mul]) }
  refine ⟨gHom, RingHom.ext hg, fun k hk => RingHom.ext fun x => hi ?_⟩
  exact (congrFun (congrArg DFunLike.coe hk) x).trans (hg x).symm

end Langlands.GroupScheme.TorsionDensity
