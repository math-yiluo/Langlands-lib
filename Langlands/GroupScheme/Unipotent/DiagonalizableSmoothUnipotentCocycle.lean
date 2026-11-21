import Langlands.GroupScheme.Unipotent.DiagonalizableUnipotentCocycle
import Langlands.Group.CoprimeNilpotentCocycle
import Langlands.GroupScheme.AutomorphicAction.BaseChange
import Langlands.GroupScheme.Torus.DiagonalizablePower
import Langlands.GroupScheme.Torus.DiagonalizablePowerDecomposition
import Langlands.GroupScheme.Torus.DiagonalizableSmoothConnectedCriteriaProof
import Langlands.GroupScheme.Rational.UnipotentPointsExponent
import Langlands.AlgebraicGeometry.PointTopology.RationalDensityExt
import Langlands.AlgebraicGeometry.PointTopology.SmoothSeparablyClosedDensity

/-! # Diagonalizable one-cocycles in smooth unipotent groups -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace Langlands.GroupScheme.diagonalizableSmoothUnipotentCocycle

/-! ### Splitting off the prime-to-`p` torsion of the character group -/

/-- A finitely generated abelian group is the direct sum of a finitely generated group whose
torsion is `p`-primary and of a finite group killed by an integer `m` prime to `p`. The
splitting is given by the projections `gᵢ` and the inclusions `sᵢ`. -/
theorem exists_split {p : ℕ} (hp : p.Prime) (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ] :
    ∃ (Λ₁ Λ₂ : Type u) (_ : AddCommGroup Λ₁) (_ : AddCommGroup Λ₂) (_ : AddGroup.FG Λ₁)
      (_ : Finite Λ₂) (g₁ : Λ →+ Λ₁) (g₂ : Λ →+ Λ₂) (s₁ : Λ₁ →+ Λ) (s₂ : Λ₂ →+ Λ) (m : ℕ),
      s₁.comp g₁ + s₂.comp g₂ = AddMonoidHom.id Λ ∧ Nat.Coprime p m ∧
      (∀ x : Λ₂, m • x = 0) ∧ (∀ x : Λ₁, IsOfFinAddOrder x → ∃ n : ℕ, p ^ n • x = 0) := by
  classical
  obtain ⟨I, A, _, _, _, ⟨b⟩⟩ := Diagonalizable.exists_freeFiniteEquiv Λ
  have hN : Nat.card A ≠ 0 := Nat.card_pos.ne'
  obtain ⟨a, m, hpm, hNm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN p hp.ne_one
  have hcop : Nat.Coprime (p ^ a) m :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, ((p ^ a : ℕ) : ℤ) * u + (m : ℤ) * v = 1 := by
    refine ⟨Nat.gcdA (p ^ a) m, Nat.gcdB (p ^ a) m, ?_⟩
    have h := Nat.gcd_eq_gcd_ab (p ^ a) m
    rw [hcop.gcd_eq_one, Nat.cast_one] at h
    exact h.symm
  have hNA : ∀ x : A, ((Nat.card A : ℕ) : ℤ) • x = 0 := fun x => by
    rw [natCast_zsmul, card_nsmul_eq_zero']
  have hNmz : ((Nat.card A : ℕ) : ℤ) = ((p ^ a : ℕ) : ℤ) * m := by
    rw [hNm, Nat.cast_mul]
  -- the idempotent `e = p ^ a * u` projects onto the prime-to-`p` part
  have hee : ∀ x : A, (((p ^ a : ℕ) : ℤ) * u) • (((p ^ a : ℕ) : ℤ) * u) • x =
      (((p ^ a : ℕ) : ℤ) * u) • x := by
    intro x
    rw [smul_smul, ← sub_eq_zero, ← sub_smul]
    have : ((p ^ a : ℕ) : ℤ) * u * (((p ^ a : ℕ) : ℤ) * u) - ((p ^ a : ℕ) : ℤ) * u =
        (-(u * v)) * ((Nat.card A : ℕ) : ℤ) := by
      rw [hNmz]
      linear_combination (((p ^ a : ℕ) : ℤ) * u) * huv
    rw [this, ← smul_smul, hNA, smul_zero]
  let π : Λ →+ A := (AddMonoidHom.snd (I → ℤ) A).comp b.toAddMonoidHom
  let j : A →+ Λ := b.symm.toAddMonoidHom.comp (AddMonoidHom.inr (I → ℤ) A)
  have hπj : ∀ x, π (j x) = x := fun x => by simp [π, j]
  have hj : Function.Injective j := Function.LeftInverse.injective hπj
  let w : A →+ A := (((p ^ a : ℕ) : ℤ) * u) • AddMonoidHom.id A
  let A₂ : AddSubgroup A := w.range
  let g₂ : Λ →+ A₂ := w.rangeRestrict.comp π
  let s₂ : A₂ →+ Λ := j.comp A₂.subtype
  let Ψ : Λ →+ Λ := s₂.comp g₂
  have hΨ : ∀ x, Ψ x = j ((((p ^ a : ℕ) : ℤ) * u) • π x) := fun x => rfl
  have hΨΨ : ∀ x, Ψ (x - Ψ x) = 0 := by
    intro x
    rw [map_sub, hΨ x, hΨ (j _), hπj, hee, sub_self]
  let g₁ : Λ →+ Ψ.ker := (AddMonoidHom.id Λ - Ψ).codRestrict Ψ.ker hΨΨ
  have hg₁ : Function.Surjective g₁ := by
    intro y
    refine ⟨y, Subtype.ext ?_⟩
    change y - Ψ y = y
    rw [y.2, sub_zero]
  have : AddGroup.FG Ψ.ker := AddGroup.fg_of_surjective hg₁
  refine ⟨Ψ.ker, A₂, inferInstance, inferInstance, this, inferInstance, g₁, g₂,
    Ψ.ker.subtype, s₂, m, ?_, (Nat.Prime.coprime_iff_not_dvd hp).2 hpm, ?_, ?_⟩
  · ext x
    change (x - Ψ x) + Ψ x = x
    rw [sub_add_cancel]
  · rintro ⟨_, y, rfl⟩
    apply Subtype.ext
    change (m : ℕ) • ((((p ^ a : ℕ) : ℤ) * u) • y) = 0
    rw [← natCast_zsmul, smul_smul, show (m : ℤ) * (((p ^ a : ℕ) : ℤ) * u) =
      u * ((Nat.card A : ℕ) : ℤ) by rw [hNmz]; ring, ← smul_smul, hNA, smul_zero]
  · intro x hx
    obtain ⟨n, hn, hnx⟩ := (isOfFinAddOrder_iff_nsmul_eq_zero).1 hx
    have hnx' : n • (x : Λ) = 0 := congrArg Subtype.val hnx
    -- the free coordinate of `x` vanishes
    have hfree : (b x).1 = 0 := by
      have h := congrArg (fun y => (b y).1) hnx'
      simp only [map_nsmul, map_zero, Prod.smul_fst, Prod.fst_zero] at h
      funext i
      have hi := congrFun h i
      simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, mul_eq_zero, Nat.cast_eq_zero] at hi
      exact hi.resolve_left hn.ne'
    have hxj : (x : Λ) = j (π x) := by
      apply b.injective
      simp only [j, π, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
        AddMonoidHom.inr_apply, AddMonoidHom.coe_snd, AddEquiv.apply_symm_apply]
      exact Prod.ext hfree rfl
    have he : (((p ^ a : ℕ) : ℤ) * u) • π x = 0 := by
      apply hj
      rw [map_zero, ← hΨ]
      exact x.2
    refine ⟨a, Subtype.ext ?_⟩
    change p ^ a • (x : Λ) = 0
    rw [hxj, ← map_nsmul]
    convert map_zero j using 2
    rw [← natCast_zsmul, show ((p ^ a : ℕ) : ℤ) =
      ((p ^ a : ℕ) : ℤ) * (((p ^ a : ℕ) : ℤ) * u) + v * ((Nat.card A : ℕ) : ℤ) by
        rw [hNmz]; linear_combination (-((p ^ a : ℕ) : ℤ)) * huv,
      add_smul, ← smul_smul, he, ← smul_smul, hNA, smul_zero, smul_zero, add_zero]

/-! ### Points of diagonalizable groups through the splitting -/

section Points

variable {k : Type u} [Field k]

set_option quotPrecheck false
local notation "𝔻" Λ => CommGroupScheme.toGrp (Diagonalizable.groupScheme (CommRingCat.of k) Λ)
local notation "T₀" => Over.mk (𝟙 (Spec (CommRingCat.of k)))
local notation "ρ" g => (Diagonalizable.restrictMap (CommRingCat.of k) g).hom.hom

/-- The morphism `D(Λ) → D(Λ')` induced by a sum of homomorphisms `Λ' → Λ` is the pointwise
product of the morphisms induced by the summands. -/
theorem comp_restrictMap_add {Λ Λ' : Type u} [AddCommGroup Λ] [AddCommGroup Λ']
    (g h : Λ' →+ Λ) {V : Over (Spec (CommRingCat.of k))} (x : V ⟶ (𝔻 Λ).X) :
    x ≫ (ρ (g + h)) = (x ≫ (ρ g)) * (x ≫ (ρ h)) := by
  apply (Diagonalizable.characterPointsEquiv (CommRingCat.of k) Λ' V).injective
  rw [map_mul]
  apply MonoidHom.ext
  intro l
  rw [MonoidHom.mul_apply]
  change Diagonalizable.characterPointsEquiv (CommRingCat.of k) Λ' V (x ≫ (ρ (g + h)))
      (.ofAdd l.toAdd) =
    Diagonalizable.characterPointsEquiv (CommRingCat.of k) Λ' V (x ≫ (ρ g)) (.ofAdd l.toAdd) *
      Diagonalizable.characterPointsEquiv (CommRingCat.of k) Λ' V (x ≫ (ρ h)) (.ofAdd l.toAdd)
  have e1 : Diagonalizable.characterPointsEquiv (CommRingCat.of k) Λ' V (x ≫ (ρ (g + h)))
      (.ofAdd l.toAdd) = Diagonalizable.characterPointsEquiv (CommRingCat.of k) Λ V x
        (.ofAdd ((g + h) l.toAdd)) :=
    Diagonalizable.pointsEquiv_restrictMap (CommRingCat.of k) (g + h) x l.toAdd
  have e2 : Diagonalizable.characterPointsEquiv (CommRingCat.of k) Λ' V (x ≫ (ρ g))
      (.ofAdd l.toAdd) = Diagonalizable.characterPointsEquiv (CommRingCat.of k) Λ V x
        (.ofAdd (g l.toAdd)) :=
    Diagonalizable.pointsEquiv_restrictMap (CommRingCat.of k) g x l.toAdd
  have e3 : Diagonalizable.characterPointsEquiv (CommRingCat.of k) Λ' V (x ≫ (ρ h))
      (.ofAdd l.toAdd) = Diagonalizable.characterPointsEquiv (CommRingCat.of k) Λ V x
        (.ofAdd (h l.toAdd)) :=
    Diagonalizable.pointsEquiv_restrictMap (CommRingCat.of k) h x l.toAdd
  rw [e1, e2, e3, AddMonoidHom.add_apply, ofAdd_add, map_mul]

/-- The morphism induced by the identity of `Λ` is the identity on points. -/
theorem comp_restrictMap_id {Λ : Type u} [AddCommGroup Λ] {V : Over (Spec (CommRingCat.of k))}
    (x : V ⟶ (𝔻 Λ).X) : x ≫ (ρ (AddMonoidHom.id Λ)) = x := by
  apply (Diagonalizable.characterPointsEquiv (CommRingCat.of k) Λ V).injective
  apply MonoidHom.ext
  intro l
  change Diagonalizable.characterPointsEquiv (CommRingCat.of k) Λ V
      (x ≫ (ρ (AddMonoidHom.id Λ))) (.ofAdd l.toAdd) =
    Diagonalizable.characterPointsEquiv (CommRingCat.of k) Λ V x (.ofAdd l.toAdd)
  exact Diagonalizable.pointsEquiv_restrictMap (CommRingCat.of k) (AddMonoidHom.id Λ) x l.toAdd

/-- Through a splitting `s₁ g₁ + s₂ g₂ = id` of `Λ`, every point of `D(Λ)` is the product of
a point coming from `D(Λ₁)` and a point coming from `D(Λ₂)`. -/
theorem eq_mul_of_split {Λ Λ₁ Λ₂ : Type u} [AddCommGroup Λ] [AddCommGroup Λ₁]
    [AddCommGroup Λ₂] (g₁ : Λ →+ Λ₁) (g₂ : Λ →+ Λ₂) (s₁ : Λ₁ →+ Λ) (s₂ : Λ₂ →+ Λ)
    (hs : s₁.comp g₁ + s₂.comp g₂ = AddMonoidHom.id Λ)
    {V : Over (Spec (CommRingCat.of k))} (x : V ⟶ (𝔻 Λ).X) :
    x = ((x ≫ (ρ s₁)) ≫ (ρ g₁)) * ((x ≫ (ρ s₂)) ≫ (ρ g₂)) := by
  calc
    x = x ≫ (ρ (AddMonoidHom.id Λ)) := (comp_restrictMap_id x).symm
    _ = x ≫ (ρ (s₁.comp g₁ + s₂.comp g₂)) := by rw [hs]
    _ = (x ≫ (ρ (s₁.comp g₁))) * (x ≫ (ρ (s₂.comp g₂))) := comp_restrictMap_add _ _ x
    _ = _ := by
      rw [← Diagonalizable.restrictMap_comp, ← Diagonalizable.restrictMap_comp, Grp.comp_hom_hom,
        Grp.comp_hom_hom, Category.assoc, Category.assoc]

/-- If `m` kills `Λ`, then `m` kills every point of `D(Λ)`. -/
theorem pow_eq_one_points {Λ : Type u} [AddCommGroup Λ] {m : ℕ} (hm : ∀ x : Λ, m • x = 0)
    {V : Over (Spec (CommRingCat.of k))} (y : V ⟶ (𝔻 Λ).X) : y ^ m = 1 := by
  apply (Diagonalizable.characterPointsEquiv (CommRingCat.of k) Λ V).injective
  rw [map_pow, map_one]
  apply MonoidHom.ext
  intro l
  rw [MonoidHom.pow_apply, MonoidHom.one_apply, ← map_pow, ← ofAdd_toAdd l, ← ofAdd_nsmul,
    hm, ofAdd_zero, map_one]

/-- Homomorphisms from a finite group to the units of a domain form a finite set. -/
theorem finite_monoidHom_units (G M : Type*) [Group G] [Finite G] [CommRing M] [IsDomain M] :
    Finite (G →* Mˣ) := by
  have hne : NeZero (Monoid.exponent G) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  let S := rootsOfUnity (Monoid.exponent G) M
  have : Finite (G →* S) := .of_injective _ DFunLike.coe_injective
  refine .of_surjective S.subtype.comp fun f ↦ ?_
  have H a : f a ∈ S := by
    rw [mem_rootsOfUnity, ← map_pow, Monoid.pow_exponent_eq_one, map_one]
  exact ⟨.codRestrict f S H, MonoidHom.ext fun _ ↦ by simp⟩

/-- A diagonalizable group with finite character group has finitely many rational points. -/
theorem finite_points (Λ : Type u) [AddCommGroup Λ] [Finite Λ] :
    Finite ((T₀) ⟶ (𝔻 Λ).X) := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  have := finite_monoidHom_units (Multiplicative Λ) k
  refine Finite.of_injective
    (fun x => (Units.map e.toRingHom.toMonoidHom).comp
      (Diagonalizable.characterPointsEquiv (CommRingCat.of k) Λ (T₀) x)) ?_
  intro x y hxy
  apply (Diagonalizable.characterPointsEquiv (CommRingCat.of k) Λ (T₀)).injective
  apply MonoidHom.ext
  intro l
  apply Units.map_injective (f := e.toRingHom.toMonoidHom) e.injective
  exact DFunLike.congr_fun hxy l

/-- A finite group all of whose elements are killed by `m`, with `m` prime to the prime
`p`, has order prime to every power of `p`. -/
theorem coprime_card_of_pow_eq_one {F : Type*} [Group F] [Finite F] {p m : ℕ} (hp : p.Prime)
    (hpm : Nat.Coprime p m) (hm : ∀ f : F, f ^ m = 1) (r : ℕ) :
    Nat.Coprime (Nat.card F) (p ^ r) := by
  refine Nat.Coprime.pow_right r (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 ?_))
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨f, hf⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have h1 : p ∣ m := hf ▸ orderOf_dvd_of_pow_eq_one (hm f)
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hpm h1)

/-- Two morphisms out of `T₀ × X`, for `X` smooth over a separably closed field, which agree
on all rational points, are equal. -/
theorem hom_ext_of_smooth [IsSepClosed k] (X Y : Over (Spec (CommRingCat.of k)))
    [Smooth X.hom] [IsSeparated Y.hom] (f g : (T₀) ⊗ X ⟶ Y)
    (h : ∀ y : (T₀) ⟶ X, lift (𝟙 (T₀)) y ≫ f = lift (𝟙 (T₀)) y ≫ g) : f = g := by
  let σ : X ⟶ (T₀) ⊗ X := lift (Over.mkIdTerminal.from _) (𝟙 _)
  have hσ : snd (T₀) X ≫ σ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, Category.id_comp]
      exact Over.mkIdTerminal.hom_ext _ _
    · rw [Category.assoc, lift_snd, Category.comp_id, Category.id_comp]
  have hyσ : ∀ y : (T₀) ⟶ X, y ≫ σ = lift (𝟙 (T₀)) y := by
    intro y
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, lift_fst]
      exact Over.mkIdTerminal.hom_ext _ _
    · rw [Category.assoc, lift_snd, lift_snd, Category.comp_id]
  have : IsReduced X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k X.left X.hom
  have hσfg : σ ≫ f = σ ≫ g := by
    refine Langlands.AlgebraicGeometry.PointTopology.hom_ext_of_denseRationalPoints
      (Langlands.AlgebraicGeometry.PointTopology.hasDenseRationalPoints_of_smooth_of_isSepClosed
        k X) ?_
    intro y
    rw [← Category.assoc, ← Category.assoc, hyσ]
    exact h y
  rw [← Category.id_comp f, ← Category.id_comp g, ← hσ, Category.assoc, Category.assoc, hσfg]

end Points

/-! ### Restricting an action to an invariant subgroup -/

/-- The restriction of an action by automorphisms to an invariant subgroup. -/
def mulAutRestrict {F G : Type*} [Group F] [Group G] (φ : F →* MulAut G) (Z : Subgroup G)
    (hZ : ∀ f, ∀ z ∈ Z, φ f z ∈ Z) : F →* MulAut Z where
  toFun f :=
    { toFun := fun z => ⟨φ f z, hZ f z z.2⟩
      invFun := fun z => ⟨φ f⁻¹ z, hZ f⁻¹ z z.2⟩
      left_inv := fun z => Subtype.ext (by
        change φ f⁻¹ (φ f z) = z
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
      right_inv := fun z => Subtype.ext (by
        change φ f (φ f⁻¹ z) = z
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply])
      map_mul' := fun z z' => Subtype.ext (map_mul (φ f) (z : G) z') }
  map_one' := MulEquiv.ext fun z => Subtype.ext (by
    change φ 1 z = z
    rw [map_one, MulAut.one_apply])
  map_mul' f f' := MulEquiv.ext fun z => Subtype.ext (by
    change φ (f * f') z = φ f (φ f' z)
    rw [map_mul, MulAut.mul_apply])

@[simp]
theorem coe_mulAutRestrict_apply {F G : Type*} [Group F] [Group G] (φ : F →* MulAut G)
    (Z : Subgroup G) (hZ : ∀ f, ∀ z ∈ Z, φ f z ∈ Z) (f : F) (z : Z) :
    ((mulAutRestrict φ Z hZ f z : Z) : G) = φ f z :=
  rfl

/-! ### Gluing a connected part and a finite part prime to the exponent -/

section Split

variable {k : Type u} [Field k]

local notation "T₀" => Over.mk (𝟙 (Spec (CommRingCat.of k)))

open AutomorphicAction

/-- Let the acting group `D` have commuting points, each a product of a point coming from
`ι₁ : D₁ → D` and a point coming from `ι₂ : D₂ → D`. Suppose that every rational cocycle of
`D₁` is a coboundary, that `D₂` has finitely many rational points, that their number is prime
to an exponent `n` of the nilpotent group `U(k)`, and that morphisms out of `T₀ × D₂` are
determined by rational points. Then every rational cocycle of `D` in `U` is a coboundary. -/
theorem exists_coboundary_of_split {D U D₁ D₂ : GroupScheme (Spec (CommRingCat.of k))}
    (a : AutomorphicAction D U) (ι₁ : D₁ ⟶ D) (ι₂ : D₂ ⟶ D)
    (hcomm : ∀ {V : Over (Spec (CommRingCat.of k))} (x y : V ⟶ D.X), x * y = y * x)
    (hgen : ∀ {V : Over (Spec (CommRingCat.of k))} (x : V ⟶ D.X),
      ∃ (y₁ : V ⟶ D₁.X) (y₂ : V ⟶ D₂.X), x = (y₁ ≫ ι₁.hom.hom) * (y₂ ≫ ι₂.hom.hom))
    (h₁ : ∀ c : (a.restrict ι₁).Cocycle (T₀),
      ∃ v : (T₀) ⟶ U.X, c = (a.restrict ι₁).coboundary v)
    [Finite ((T₀) ⟶ D₂.X)] [Group.IsNilpotent ((T₀) ⟶ U.X)] {n : ℕ}
    (hn : ∀ x : (T₀) ⟶ U.X, x ^ n = 1) (hcop : Nat.Coprime (Nat.card ((T₀) ⟶ D₂.X)) n)
    (hext : ∀ f g : (T₀) ⊗ D₂.X ⟶ U.X,
      (∀ y : (T₀) ⟶ D₂.X, lift (𝟙 (T₀)) y ≫ f = lift (𝟙 (T₀)) y ≫ g) → f = g)
    (c : a.Cocycle (T₀)) : ∃ v : (T₀) ⟶ U.X, c = a.coboundary v := by
  obtain ⟨v, hv⟩ := h₁ (c.precomp ι₁)
  set c₁ := Cocycle.conjugate v⁻¹ c with hc₁
  -- `c₁` is trivial on `D₁`
  have htriv₁ : ∀ {V : Over (Spec (CommRingCat.of k))} (b : V ⟶ T₀) (y : V ⟶ D₁.X),
      c₁.eval b (y ≫ ι₁.hom.hom) = 1 := by
    intro V b y
    have h := congrArg (fun d => Cocycle.eval d b y) hv
    simp only [Cocycle.eval_precomp, eval_coboundary, restrict_act] at h
    rw [hc₁, Cocycle.eval_conjugate, h]
    simp only [GrpObj.comp_inv, a.act_inv, inv_inv]
    group
  -- the values of `c₁` on `D₂` are fixed by `D₁`
  have hfix : ∀ {V : Over (Spec (CommRingCat.of k))} (b : V ⟶ T₀) (y : V ⟶ D₂.X),
      c₁.eval b (y ≫ ι₂.hom.hom) ∈ (a.restrict ι₁).fixedSubgroup.carrier V := by
    intro V b y
    rw [mem_fixedSubgroup]
    intro T' b' h
    rw [restrict_act, Cocycle.eval_naturality]
    have hXY := c₁.eval_mul (b' ≫ b) (h ≫ ι₁.hom.hom) (b' ≫ y ≫ ι₂.hom.hom)
    have hYX := c₁.eval_mul (b' ≫ b) (b' ≫ y ≫ ι₂.hom.hom) (h ≫ ι₁.hom.hom)
    rw [hcomm (h ≫ ι₁.hom.hom), hYX, htriv₁, a.act_one, mul_one, one_mul] at hXY
    exact hXY.symm
  -- the rational points of `D₂` act on the `D₁`-fixed rational points of `U`
  let Z := (a.restrict ι₁).fixedSubgroup.carrier (T₀)
  have hZ : ∀ f : (T₀) ⟶ D₂.X, ∀ z ∈ Z, (a.restrict ι₂).pointsAction (T₀) f z ∈ Z := by
    intro f z hz
    rw [mem_fixedSubgroup]
    intro T' b' h
    have hz' := (a.restrict ι₁).mem_fixedSubgroup.1 hz T' b' h
    rw [restrict_act] at hz'
    simp only [pointsAction_apply, restrict_act]
    rw [a.naturality, ← a.act_mul_left, hcomm, a.act_mul_left, hz']
  let φ := mulAutRestrict ((a.restrict ι₂).pointsAction (T₀)) Z hZ
  let cF : ((T₀) ⟶ D₂.X) → Z := fun f => ⟨c₁.eval (𝟙 _) (f ≫ ι₂.hom.hom), hfix (𝟙 _) f⟩
  have hcF : ∀ f f', cF (f * f') = cF f * φ f (cF f') := by
    intro f f'
    apply Subtype.ext
    simp only [cF, φ, Subgroup.coe_mul, coe_mulAutRestrict_apply, pointsAction_apply,
      restrict_act]
    rw [MonObj.mul_comp, c₁.eval_mul]
  obtain ⟨g₀, hg₀⟩ := Langlands.Group.CoprimeNilpotentCocycle.exists_coboundary Z φ
    (fun x => Subtype.ext (by rw [Subgroup.coe_pow, hn, Subgroup.coe_one])) hcop cF hcF
  set g : (T₀) ⟶ U.X := (g₀ : (T₀) ⟶ U.X) with hg
  have hg₀' : ∀ f : (T₀) ⟶ D₂.X,
      c₁.eval (𝟙 _) (f ≫ ι₂.hom.hom) = g * (a.act (f ≫ ι₂.hom.hom) g)⁻¹ := by
    intro f
    have := congrArg Subtype.val (hg₀ f)
    simpa [cF, φ] using this
  set c₂ := Cocycle.conjugate g⁻¹ c₁ with hc₂
  -- `c₂` is trivial on `D₂`, first on rational points, then everywhere
  have htriv₂ : (c₂.precomp ι₂).hom = 1 := by
    apply hext
    intro y
    rw [MonObj.comp_one]
    change (c₂.precomp ι₂).eval (𝟙 _) y = 1
    rw [Cocycle.eval_precomp, hc₂, Cocycle.eval_conjugate, Category.id_comp, hg₀' y]
    simp only [inv_inv]
    group
  have hD₂ : ∀ {V : Over (Spec (CommRingCat.of k))} (b : V ⟶ T₀) (y : V ⟶ D₂.X),
      c₂.eval b (y ≫ ι₂.hom.hom) = 1 := by
    intro V b y
    rw [← Cocycle.eval_precomp]
    change lift b y ≫ (c₂.precomp ι₂).hom = 1
    rw [htriv₂, MonObj.comp_one]
  -- `c₂` is still trivial on `D₁`, since `g` is fixed by `D₁`
  have hD₁ : ∀ {V : Over (Spec (CommRingCat.of k))} (b : V ⟶ T₀) (y : V ⟶ D₁.X),
      c₂.eval b (y ≫ ι₁.hom.hom) = 1 := by
    intro V b y
    have hfixg : a.act (y ≫ ι₁.hom.hom) (b ≫ g) = b ≫ g := by
      have := (a.restrict ι₁).mem_fixedSubgroup.1 g₀.2 V b y
      rwa [restrict_act] at this
    rw [hc₂, Cocycle.eval_conjugate, htriv₁]
    simp only [GrpObj.comp_inv, inv_inv, hfixg]
    group
  have hc₂triv : c₂ = Cocycle.trivial (T₀) := by
    apply Cocycle.eval_ext
    intro V b x
    obtain ⟨y₁, y₂, rfl⟩ := hgen x
    rw [c₂.eval_mul, hD₁, hD₂, a.act_one, mul_one, Cocycle.eval_trivial]
  refine ⟨v * g, ?_⟩
  rw [← Cocycle.conjugate_coboundary, AutomorphicAction.coboundary, ← hc₂triv, hc₂,
    Cocycle.conjugate_conjugate_inv, hc₁, Cocycle.conjugate_conjugate_inv]

end Split

/-! ### The vanishing theorem -/

section Main

variable {k : Type u} [Field k]

local notation "𝔻" Λ => CommGroupScheme.toGrp (Diagonalizable.groupScheme (CommRingCat.of k) Λ)
local notation "T₀" => Over.mk (𝟙 (Spec (CommRingCat.of k)))

/-- In characteristic `p`, over an algebraically closed field, every rational one-cocycle of
a diagonalizable group `D(Λ)`, with `Λ` finitely generated, in a smooth affine unipotent
group is a coboundary. -/
theorem exists_coboundary_of_charP [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ]
    (U : GroupScheme (Spec (CommRingCat.of k))) [Smooth U.X.hom] [IsAffineHom U.X.hom]
    (hU : IsUnipotent U) (a : AutomorphicAction (𝔻 Λ) U) (c : a.Cocycle (T₀)) :
    ∃ v : (T₀) ⟶ U.X, c = a.coboundary v := by
  have hp : p.Prime := Fact.out
  have : ExpChar k p := ExpChar.prime hp
  obtain ⟨Λ₁, Λ₂, _, _, _, _, g₁, g₂, s₁, s₂, m, hs, hpm, hm, htors⟩ := exists_split hp Λ
  have hconn : ConnectedSpace (𝔻 Λ₁).X.left :=
    (Diagonalizable.diagonalizableSmoothConnectedCriteria k p Λ₁).1.2 htors
  have hsmooth : Smooth (𝔻 Λ₂).X.hom := by
    refine (Diagonalizable.diagonalizableSmoothConnectedCriteria k p Λ₂).2.1.2 fun x hx => ?_
    have h1 : addOrderOf x ∣ Nat.gcd p m :=
      Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hx) (addOrderOf_dvd_of_nsmul_eq_zero (hm x))
    rw [hpm.gcd_eq_one, Nat.dvd_one, AddMonoid.addOrderOf_eq_one_iff] at h1
    exact h1
  have : Finite ((T₀) ⟶ (𝔻 Λ₂).X) := finite_points Λ₂
  have : Group.IsNilpotent ((T₀) ⟶ U.X) := isNilpotent_points_of_isUnipotent hU (T₀)
  have : IsSeparated U.X.hom := IsSeparated.of_isAffineHom U.X.hom
  obtain ⟨r, hr⟩ := exists_hasUniformPowerExponent_of_isUnipotent p hU
  exact exists_coboundary_of_split a (Diagonalizable.restrictMap (CommRingCat.of k) g₁)
    (Diagonalizable.restrictMap (CommRingCat.of k) g₂) (fun x y => mul_comm x y)
    (fun x => ⟨_, _, eq_mul_of_split g₁ g₂ s₁ s₂ hs x⟩)
    (fun c' => diagonalizableUnipotentCocycle.exists_coboundary_of_smooth Λ₁ (Or.inl hconn)
      U hU _ c')
    (hr (T₀)) (coprime_card_of_pow_eq_one hp hpm (pow_eq_one_points hm) r)
    (hom_ext_of_smooth _ _) c

end Main

/-- Over an algebraically closed field, every rational one-cocycle of a diagonalizable group
`D(Λ)`, with `Λ` finitely generated, in a smooth affine unipotent group is a coboundary. -/
def VanishingStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ]
    (U : GroupScheme (Spec (CommRingCat.of k))) [Smooth U.X.hom] [IsAffineHom U.X.hom],
    IsUnipotent U →
    ∀ (a : AutomorphicAction (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp U)
      (c : a.Cocycle (Over.mk (𝟙 (Spec (CommRingCat.of k))))),
      ∃ v : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X, c = a.coboundary v

/-- Diagonalizable one-cocycles in smooth affine unipotent groups are coboundaries. -/
theorem exists_coboundary : VanishingStatement.{u} := by
  intro k _ _ Λ _ _ U _ _ hU a c
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp
  · have : Fact (ringChar k).Prime := ⟨hp⟩
    exact exists_coboundary_of_charP (ringChar k) Λ U hU a c
  · have : CharZero k := (CharP.ringChar_zero_iff_CharZero k).1 hp
    exact diagonalizableUnipotentCocycle.exists_coboundary_of_smooth Λ (Or.inr this) U hU a c

end Langlands.GroupScheme.diagonalizableSmoothUnipotentCocycle
