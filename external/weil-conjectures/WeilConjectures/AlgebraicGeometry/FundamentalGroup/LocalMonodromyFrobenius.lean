/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalMonodromy
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius.FiberMapPow
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius.Points
public import WeilConjectures.Compactification.Defs

/-!
# Local monodromy of Frobenius-fixed torsors on the geometric fibre of a curve

Let `U₀ ⊆ C₀` be a smooth curve over a finite field `K = 𝔽_q` in a smooth compactification, with
geometric fibres `U ⊆ C`, and let `V ⊆ C` be an open with `V ∖ U = {z}`. A positive power
`Φ ^ m` of the geometric Galois Frobenius fixes the closed point `z`
(`AlgebraicGeometry.Scheme.Hom.exists_geometricGaloisFrobenius_pow_apply_eq`), and acts on the
roots of unity of `𝔽̄_q` through `Q = q ^ m`. Hence `Q - 1` kills the local monodromy at `z` of a
`ℤ / N`-torsor on `U` which is fixed by `Φ ^ m`
(`AlgebraicGeometry.Scheme.EtaleTorsor.exists_natCast_sub_one_mul_monodromy_eq_zero`). This is
the Frobenius action on the boundary module of blueprint `proposition-no-fixed-class-degree-one--1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

/-- If `Q ≥ 2` and `ℓ` is a prime, there is a power `ℓ ^ v` (the `ℓ`-part of `Q - 1`) such that
in every `ZMod (ℓ ^ n)`, an element killed by `Q - 1` is killed by `ℓ ^ v`. -/
theorem ZMod.exists_natCast_pow_mul_eq_zero_of_natCast_sub_one_mul_eq_zero {l Q : ℕ}
    (hl : l.Prime) (hQ : 2 ≤ Q) :
    ∃ v : ℕ, ∀ (n : ℕ) (a : ZMod (l ^ n)), ((Q : ZMod (l ^ n)) - 1) * a = 0 →
      ((l ^ v : ℕ) : ZMod (l ^ n)) * a = 0 := by
  obtain ⟨v, w, hw, hQw⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := Q - 1) (by omega) l hl.ne_one
  refine ⟨v, fun n a ha ↦ ?_⟩
  have hcop : w.Coprime (l ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hl).2 hw))
  rw [← Nat.cast_one, ← Nat.cast_sub (by omega), hQw, Nat.cast_mul, mul_right_comm] at ha
  exact ((ZMod.isUnit_iff_coprime w _).2 hcop).mul_left_eq_zero.1 ha

/-- If an automorphism `ψ` of `X` lies over an automorphism `E` of `Y` along `π`, then so do
their powers. -/
theorem CategoryTheory.Aut.pow_hom_comp_eq_comp_pow_hom {C : Type*} [Category C] {X Y : C}
    (π : X ⟶ Y) (ψ : Aut X) (E : Aut Y) (h : ψ.asIso.hom ≫ π = π ≫ E.asIso.hom) (m : ℕ) :
    (ψ ^ m).asIso.hom ≫ π = π ≫ (E ^ m).asIso.hom := by
  induction m with
  | zero => exact (Category.id_comp _).trans (Category.comp_id _).symm
  | succ m ih =>
    rw [pow_succ, pow_succ, Aut.mul_asIso, Aut.mul_asIso, Iso.trans_hom, Iso.trans_hom,
      Category.assoc, ih, reassoc_of% h]

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- A closed point of the geometric fibre of a scheme locally of finite type over a finite field
is fixed by a positive power of the geometric Galois Frobenius: it lies over a closed point with
finite residue field. -/
theorem exists_geometricGaloisFrobenius_pow_apply_eq [Finite k] [LocallyOfFiniteType f]
    (z : f.geometricFiber) (hz : IsClosed ({z} : Set f.geometricFiber)) :
    ∃ m : ℕ, 1 ≤ m ∧ (f.geometricGaloisFrobenius ^ m).asIso.hom z = z := by
  obtain ⟨s, hs⟩ := f.geometricFiberToAlgebraicClosure.exists_spec_base_eq_of_isClosed z hz
  have hsz : (s ≫ f.geometricFiberProj).base (IsLocalRing.closedPoint _) =
      f.geometricFiberProj z := by
    rw [← hs]
    rfl
  have hx : (s ≫ f.geometricFiberProj).base (IsLocalRing.closedPoint _) ∈ X.finitePoints := by
    have hc : IsClosed ({f.geometricFiberProj z} : Set X) := by
      simpa using f.geometricFiberProj.isClosedMap _ hz
    let := (f.residueFieldAlgebraMap (f.geometricFiberProj z)).toAlgebra
    have := f.finite_residueField_of_isClosed _ hc
    rw [hsz]
    exact X.mem_finitePoints.mpr (Module.finite_of_finite k)
  obtain ⟨g, j, hj, hgj, -⟩ := f.exists_iso_comp_eq_comp_geometricGaloisFrobenius_pow s s rfl hx
  refine ⟨j, hj, ?_⟩
  have h := congrArg (fun t ↦ t.base (IsLocalRing.closedPoint (AlgebraicClosure k))) hgj
  rw [← hs]
  refine h.symm.trans ?_
  exact congrArg s.base (Subsingleton.elim _ _)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.EtaleTorsor

open FiniteEtale

variable {K : Type u} [Field K] [Finite K]

/-- Blueprint `proposition-no-fixed-class-degree-one--1`: the Frobenius acts on the boundary module
`ℤ / N (-1)` at a boundary point `z` through `Q = q ^ m`, for a power `Φ ^ m` fixing `z`.

Let `U₀ ⊆ C₀` be a smooth curve over `K = 𝔽_q` in a compactification `c` by a smooth curve,
with geometric fibres `U ⊆ C`, and let `V ⊆ C` be an open containing `U` with `V ∖ U = {z}`.
There is `m ≥ 1` such that for every `ℤ / N`-torsor `T` on `U`, `N` invertible in `K`, which is
fixed by `Φ ^ m` (through `ψ`), `q ^ m - 1` kills the monodromy of `T` on the kernel of
`π₁(U) → π₁(V)`. -/
theorem exists_natCast_sub_one_mul_monodromy_eq_zero {U : Scheme.{u}}
    (p : U ⟶ Spec (.of K)) (c : Compactification p) [IsCurve c.g]
    [SmoothOfRelativeDimension 1 c.g] [ConnectedSpace p.geometricFiber]
    [ConnectedSpace c.g.geometricFiber] {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
    (s : Spec (.of Ω') ⟶ p.geometricFiber)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]
    (V : c.g.geometricFiber.Opens)
    (hV : Set.range (p.geometricFiberMap c.i c.comm.symm).base ⊆ V) (z : c.g.geometricFiber)
    (hz : (V : Set c.g.geometricFiber) \ Set.range (p.geometricFiberMap c.i c.comm.symm).base =
      {z}) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ {N : ℕ} [NeZero N], (N : AlgebraicClosure K) ≠ 0 →
      ∀ (T : EtaleTorsor (ULift.{u + 1} (ZMod N)) p.geometricFiber) (ψ : T.P ≅ T.P),
        ψ.hom ≫ T.π = T.π ≫ (p.geometricGaloisFrobenius ^ m).asIso.hom →
        (∀ a, T.vadd a ≫ ψ.hom = ψ.hom ≫ T.vadd a) →
        ∀ g ∈ fixingSubgroup s (IsOpenImmersion.lift V.ι (p.geometricFiberMap c.i c.comm.symm)
            (by rwa [Scheme.Opens.range_ι])) G,
          (((Nat.card K ^ m : ℕ) : ZMod N) - 1) * (T.monodromy s G g).toAdd.down = 0 := by
  let := Fintype.ofFinite K
  set q := c.g.geometricFiberToAlgebraicClosure
  set j := p.geometricFiberMap c.i c.comm.symm
  have : SmoothOfRelativeDimension 1 q :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (Limits.pullback.snd c.g _))
  have : IsSeparated q := inferInstanceAs (IsSeparated (Limits.pullback.snd c.g _))
  have : IsCurve q :=
    { krullDim_le_one := by exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension q 1 }
  have : Smooth q := SmoothOfRelativeDimension.smooth 1 q
  have := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsRegular c.g.geometricFiber := IsRegular.of_smooth q
  have : IrreducibleSpace c.g.geometricFiber := IsRegular.irreducibleSpace _
  -- the boundary point `z` is closed, hence fixed by a power of the Frobenius
  obtain ⟨u₀⟩ : Nonempty p.geometricFiber := inferInstance
  have hzV : z ∈ (V : Set c.g.geometricFiber) \ Set.range j.base := hz ▸ rfl
  have hzj : z ∉ Set.range j.base := hzV.2
  have hzc : IsClosed ({z} : Set c.g.geometricFiber) :=
    j.isOpenEmbedding.isOpen_range.isClosed_singleton_of_mem_compl
      (IsCurve.krullDim_le_one (f := q)) ⟨_, u₀, rfl⟩ hzj
  obtain ⟨m, hm, hmz⟩ := c.g.exists_geometricGaloisFrobenius_pow_apply_eq z hzc
  refine ⟨m, hm, fun {N} _ hN T ψ hψπ hψv g hg ↦ ?_⟩
  -- the power `Φ ^ m` is semilinear over `σ₀ = φ ^ m`, with `σ₀ x ^ (q ^ m) = x`
  set φ := FiniteField.geometricFrobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)
  have hσ₀ : (c.g.geometricGaloisFrobenius ^ m).asIso.hom ≫ q =
      q ≫ Spec.map (CommRingCat.ofHom ((φ ^ m).toRingEquiv : AlgebraicClosure K →+* _)) := by
    rw [Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberToAlgebraicClosure,
      specGeometricFrobenius_pow_hom]
    rfl
  have hQ (x : AlgebraicClosure K) : (φ ^ m).toRingEquiv x ^ (Nat.card K ^ m) = x := by
    have h := congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate K
      (AlgebraicClosure K) m) ((φ ^ m) x)
    rw [Nat.card_eq_fintype_card]
    refine h.symm.trans ?_
    have hφ : φ = (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K))⁻¹ := rfl
    rw [← AlgEquiv.coe_pow, hφ, inv_pow,
      AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  exact natCast_sub_one_mul_monodromy_eq_zero (p := q) (j := j) V hV z hz
    (c.g.geometricGaloisFrobenius ^ m).asIso (p.geometricGaloisFrobenius ^ m).asIso
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_pow c.i c.comm.symm m).symm hmz
    (φ ^ m).toRingEquiv hσ₀ _ hQ s G hN T ψ hψπ hψv g hg

end AlgebraicGeometry.Scheme.EtaleTorsor
