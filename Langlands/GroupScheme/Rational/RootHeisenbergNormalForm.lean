import Langlands.GroupScheme.Rational.RootDoubleCommutatorBilinear
import Langlands.GroupScheme.Rational.SplitTorusEquivariantSection
import Langlands.GroupScheme.Rational.AffineVectorExtension

/-! # The Heisenberg normal form of a multipliable relative root group

For a multipliable relative root `a` with no relative root `n • a`, `n ≥ 3`, the root group
`U = U_a` has a torus-equivariant section `σ : U_a / U_{2a} ⟶ U_a` of schemes. In it the group
law reads `σ(x) σ(y) = β(x, y) σ(x y)` for a cocycle `β` with values in `U_{2a}`. The cocycle
is bilinear in weight vector coordinates, and the commutator pairing is `β(x, y) β(y, x)⁻¹`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj LaurentPolynomial Polynomial

namespace Langlands.GroupScheme.RelativeRoot

section Laurent

variable {A : Type u} [CommRing A]

/-- The nonnegative part of `t q(t⁻¹)` is the reflection of the terms of `q` of degree at
most one. -/
theorem trunc_T_one_mul_invert_toLaurent (q : A[X]) :
    LaurentPolynomial.trunc
        (LaurentPolynomial.T 1 * LaurentPolynomial.invert (Polynomial.toLaurent q)) =
      Polynomial.C (q.coeff 0) * Polynomial.X + Polynomial.C (q.coeff 1) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, mul_add, map_add, hp, hq]
    simp only [Polynomial.coeff_add, map_add]
    ring
  | monomial n r =>
    have hm : LaurentPolynomial.T 1 * LaurentPolynomial.invert
        (LaurentPolynomial.C r * LaurentPolynomial.T (n : ℤ) : A[T;T⁻¹]) =
        LaurentPolynomial.C r * LaurentPolynomial.T (1 + -(n : ℤ)) := by
      rw [map_mul LaurentPolynomial.invert, LaurentPolynomial.invert_C,
        LaurentPolynomial.invert_T, ← mul_assoc, (LaurentPolynomial.commute_T 1 _).eq,
        mul_assoc, ← LaurentPolynomial.T_add]
    rw [Polynomial.toLaurent_C_mul_T, hm, LaurentPolynomial.trunc_C_mul_T]
    rcases n with _ | _ | n
    · simp [Polynomial.C_mul_X_eq_monomial]
    · simp [Polynomial.coeff_monomial]
    · have h : ¬ (0 : ℤ) ≤ 1 + -((n + 2 : ℕ) : ℤ) := by omega
      simp only [h, ite_false, Polynomial.coeff_monomial]
      simp

/-- If `p(t) = t q(t⁻¹)`, then `p` is the reflection of the terms of `q` of degree at most
one. -/
theorem eq_of_toLaurent_eq_T_one_mul_invert {p q : A[X]}
    (h : Polynomial.toLaurent p =
      LaurentPolynomial.T 1 * LaurentPolynomial.invert (Polynomial.toLaurent q)) :
    p = Polynomial.C (q.coeff 0) * Polynomial.X + Polynomial.C (q.coeff 1) := by
  rw [← Polynomial.trunc_toLaurent p, h, trunc_T_one_mul_invert_toLaurent]

end Laurent

section Additivity

variable {k : Type u} [Field k] {V W : GroupScheme (Spec (CommRingCat.of k))} {d m : ℕ}
    {e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤))}
    {e' : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ W.X) ≃* Multiplicative (Fin m → Γ(T.left, ⊤))}
    {P : V.X ⊗ V.X ⟶ W.X}

/-- The constant coefficient is evaluation at zero. -/
theorem aevalTower_id_zero {A : Type u} [CommRing A] [Algebra k A] (p : A[X]) :
    Polynomial.aevalTower (AlgHom.id k A) 0 p = p.coeff 0 := by
  have h : (Polynomial.aevalTower (AlgHom.id k A) 0 : A[X] →+* A) =
      Polynomial.constantCoeff := by
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp
  exact RingHom.congr_fun h p

/-- **Additivity from scalar linearity.** A pairing that is linear over every coefficient
algebra in its first argument, in coordinates, is additive in that argument. -/
theorem coordinatePairing_add_left (he : IsNaturalVectorCoordinates e)
    (he' : IsNaturalVectorCoordinates e')
    (hsmul : ∀ (A : Type u) [CommRing A] [Algebra k A] (r : A) (x y : Fin d → A),
      coordinatePairing e e' P (r • x) y = r • coordinatePairing e e' P x y)
    {A : Type u} [CommRing A] [Algebra k A] (x x' y : Fin d → A) :
    coordinatePairing e e' P (x + x') y =
      coordinatePairing e e' P x y + coordinatePairing e e' P x' y := by
  obtain ⟨Xx, hXx⟩ : ∃ Xx : Fin d → A[X],
      Xx = fun j => Polynomial.X * Polynomial.C (x j) + Polynomial.C (x' j) := ⟨_, rfl⟩
  obtain ⟨Xx', hXx'⟩ : ∃ Xx' : Fin d → A[X],
      Xx' = fun j => Polynomial.C (x j) + Polynomial.X * Polynomial.C (x' j) := ⟨_, rfl⟩
  obtain ⟨Cy, hCy⟩ : ∃ Cy : Fin d → A[X], Cy = fun j => Polynomial.C (y j) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = coordinatePairing e e' P Xx Cy := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = coordinatePairing e e' P Xx' Cy := ⟨_, rfl⟩
  let ev (a : A) : A[X] →ₐ[k] A := Polynomial.aevalTower (AlgHom.id k A) a
  have hCy' (a : A) : (fun j => ev a (Cy j)) = y := by
    subst hCy
    funext j
    simp only [ev, Polynomial.aevalTower_C, AlgHom.id_apply]
  have hevG (a : A) : coordinatePairing e e' P (a • x + x') y = fun l => ev a (G l) := by
    have h := coordinatePairing_naturality (P := P) he he' (ev a) Xx Cy
    have h1 : (fun j => ev a (Xx j)) = a • x + x' := by
      subst hXx
      funext j
      simp only [ev, map_add, map_mul, Polynomial.aevalTower_X, Polynomial.aevalTower_C,
        AlgHom.id_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [h1, hCy'] at h
    rw [h, hG]
  have hevK (a : A) : coordinatePairing e e' P (x + a • x') y = fun l => ev a (K l) := by
    have h := coordinatePairing_naturality (P := P) he he' (ev a) Xx' Cy
    have h1 : (fun j => ev a (Xx' j)) = x + a • x' := by
      subst hXx'
      funext j
      simp only [ev, map_add, map_mul, Polynomial.aevalTower_X, Polynomial.aevalTower_C,
        AlgHom.id_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [h1, hCy'] at h
    rw [h, hK]
  -- the Laurent relation `G(t) = t K(t⁻¹)`
  have hrel (l : Fin m) : Polynomial.toLaurent (G l) =
      LaurentPolynomial.T 1 * LaurentPolynomial.invert (Polynomial.toLaurent (K l)) := by
    let Lx : Fin d → A[T;T⁻¹] := fun j => laurentCAlgHom (k := k) A (x j)
    let Lx' : Fin d → A[T;T⁻¹] := fun j => laurentCAlgHom (k := k) A (x' j)
    let Ly : Fin d → A[T;T⁻¹] := fun j => laurentCAlgHom (k := k) A (y j)
    let ψ := laurentPowerAlgHom (k := k) A 1
    let ρ : A[X] →ₐ[k] A[T;T⁻¹] :=
      Polynomial.aevalTower (laurentCAlgHom (k := k) A) (LaurentPolynomial.T (-1))
    have hψX : (fun j => ψ (Xx j)) = (LaurentPolynomial.T 1 : A[T;T⁻¹]) • Lx + Lx' := by
      subst hXx
      funext j
      simp [ψ, Lx, Lx', laurentPowerAlgHom]
    have hψC : (fun j => ψ (Cy j)) = Ly := by
      subst hCy
      funext j
      simp [ψ, Ly, laurentPowerAlgHom]
    have hρX : (fun j => ρ (Xx' j)) = Lx + (LaurentPolynomial.T (-1) : A[T;T⁻¹]) • Lx' := by
      subst hXx'
      funext j
      simp [ρ, Lx, Lx']
    have hρC : (fun j => ρ (Cy j)) = Ly := by
      subst hCy
      funext j
      simp [ρ, Ly]
    have hψ := coordinatePairing_naturality (P := P) he he' ψ Xx Cy
    rw [hψX, hψC, ← hG] at hψ
    have hρ := coordinatePairing_naturality (P := P) he he' ρ Xx' Cy
    rw [hρX, hρC, ← hK] at hρ
    have hTT : (LaurentPolynomial.T 1 : A[T;T⁻¹]) •
        (Lx + (LaurentPolynomial.T (-1) : A[T;T⁻¹]) • Lx') =
        (LaurentPolynomial.T 1 : A[T;T⁻¹]) • Lx + Lx' := by
      rw [smul_add, smul_smul, ← LaurentPolynomial.T_add]
      norm_num [LaurentPolynomial.T_zero]
    have hs := hsmul (A[T;T⁻¹]) (LaurentPolynomial.T 1)
      (Lx + (LaurentPolynomial.T (-1) : A[T;T⁻¹]) • Lx') Ly
    rw [hTT, hψ, hρ] at hs
    have h := congrFun hs l
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [← laurentPowerAlgHom_one_apply (k := k), ← aevalTower_laurentCAlgHom_T_neg_one (k := k)]
    exact h
  have hGK (l : Fin m) := eq_of_toLaurent_eq_T_one_mul_invert (hrel l)
  have hval (a : A) (l : Fin m) : ev a (G l) = (K l).coeff 0 * a + (K l).coeff 1 := by
    conv_lhs => rw [hGK l]
    simp only [ev, map_add, map_mul, Polynomial.aevalTower_X, Polynomial.aevalTower_C,
      AlgHom.id_apply]
  have hx : coordinatePairing e e' P x y = fun l => (K l).coeff 0 := by
    have h := hevK 0
    rw [zero_smul, add_zero] at h
    rw [h]
    funext l
    exact aevalTower_id_zero _
  have hx' : coordinatePairing e e' P x' y = fun l => (K l).coeff 1 := by
    have h := hevG 0
    rw [zero_smul, zero_add] at h
    rw [h]
    funext l
    rw [hval 0 l, mul_zero, zero_add]
  have hsum := hevG 1
  rw [one_smul] at hsum
  rw [hsum, hx, hx']
  funext l
  rw [hval 1 l, Pi.add_apply, mul_one]

/-- **Additivity from scalar linearity**, in the second argument. -/
theorem coordinatePairing_add_right (he : IsNaturalVectorCoordinates e)
    (he' : IsNaturalVectorCoordinates e')
    (hsmul : ∀ (A : Type u) [CommRing A] [Algebra k A] (r : A) (x y : Fin d → A),
      coordinatePairing e e' P x (r • y) = r • coordinatePairing e e' P x y)
    {A : Type u} [CommRing A] [Algebra k A] (x y y' : Fin d → A) :
    coordinatePairing e e' P x (y + y') =
      coordinatePairing e e' P x y + coordinatePairing e e' P x y' := by
  obtain ⟨Yy, hYy⟩ : ∃ Yy : Fin d → A[X],
      Yy = fun j => Polynomial.X * Polynomial.C (y j) + Polynomial.C (y' j) := ⟨_, rfl⟩
  obtain ⟨Yy', hYy'⟩ : ∃ Yy' : Fin d → A[X],
      Yy' = fun j => Polynomial.C (y j) + Polynomial.X * Polynomial.C (y' j) := ⟨_, rfl⟩
  obtain ⟨Cx, hCx⟩ : ∃ Cx : Fin d → A[X], Cx = fun j => Polynomial.C (x j) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = coordinatePairing e e' P Cx Yy := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = coordinatePairing e e' P Cx Yy' := ⟨_, rfl⟩
  let ev (a : A) : A[X] →ₐ[k] A := Polynomial.aevalTower (AlgHom.id k A) a
  have hCx' (a : A) : (fun j => ev a (Cx j)) = x := by
    subst hCx
    funext j
    simp only [ev, Polynomial.aevalTower_C, AlgHom.id_apply]
  have hevG (a : A) : coordinatePairing e e' P x (a • y + y') = fun l => ev a (G l) := by
    have h := coordinatePairing_naturality (P := P) he he' (ev a) Cx Yy
    have h1 : (fun j => ev a (Yy j)) = a • y + y' := by
      subst hYy
      funext j
      simp only [ev, map_add, map_mul, Polynomial.aevalTower_X, Polynomial.aevalTower_C,
        AlgHom.id_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [h1, hCx'] at h
    rw [h, hG]
  have hevK (a : A) : coordinatePairing e e' P x (y + a • y') = fun l => ev a (K l) := by
    have h := coordinatePairing_naturality (P := P) he he' (ev a) Cx Yy'
    have h1 : (fun j => ev a (Yy' j)) = y + a • y' := by
      subst hYy'
      funext j
      simp only [ev, map_add, map_mul, Polynomial.aevalTower_X, Polynomial.aevalTower_C,
        AlgHom.id_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [h1, hCx'] at h
    rw [h, hK]
  have hrel (l : Fin m) : Polynomial.toLaurent (G l) =
      LaurentPolynomial.T 1 * LaurentPolynomial.invert (Polynomial.toLaurent (K l)) := by
    let Lx : Fin d → A[T;T⁻¹] := fun j => laurentCAlgHom (k := k) A (x j)
    let Ly : Fin d → A[T;T⁻¹] := fun j => laurentCAlgHom (k := k) A (y j)
    let Ly' : Fin d → A[T;T⁻¹] := fun j => laurentCAlgHom (k := k) A (y' j)
    let ψ := laurentPowerAlgHom (k := k) A 1
    let ρ : A[X] →ₐ[k] A[T;T⁻¹] :=
      Polynomial.aevalTower (laurentCAlgHom (k := k) A) (LaurentPolynomial.T (-1))
    have hψY : (fun j => ψ (Yy j)) = (LaurentPolynomial.T 1 : A[T;T⁻¹]) • Ly + Ly' := by
      subst hYy
      funext j
      simp [ψ, Ly, Ly', laurentPowerAlgHom]
    have hψC : (fun j => ψ (Cx j)) = Lx := by
      subst hCx
      funext j
      simp [ψ, Lx, laurentPowerAlgHom]
    have hρY : (fun j => ρ (Yy' j)) = Ly + (LaurentPolynomial.T (-1) : A[T;T⁻¹]) • Ly' := by
      subst hYy'
      funext j
      simp [ρ, Ly, Ly']
    have hρC : (fun j => ρ (Cx j)) = Lx := by
      subst hCx
      funext j
      simp [ρ, Lx]
    have hψ := coordinatePairing_naturality (P := P) he he' ψ Cx Yy
    rw [hψY, hψC, ← hG] at hψ
    have hρ := coordinatePairing_naturality (P := P) he he' ρ Cx Yy'
    rw [hρY, hρC, ← hK] at hρ
    have hTT : (LaurentPolynomial.T 1 : A[T;T⁻¹]) •
        (Ly + (LaurentPolynomial.T (-1) : A[T;T⁻¹]) • Ly') =
        (LaurentPolynomial.T 1 : A[T;T⁻¹]) • Ly + Ly' := by
      rw [smul_add, smul_smul, ← LaurentPolynomial.T_add]
      norm_num [LaurentPolynomial.T_zero]
    have hs := hsmul (A[T;T⁻¹]) (LaurentPolynomial.T 1) Lx
      (Ly + (LaurentPolynomial.T (-1) : A[T;T⁻¹]) • Ly')
    rw [hTT, hψ, hρ] at hs
    have h := congrFun hs l
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [← laurentPowerAlgHom_one_apply (k := k), ← aevalTower_laurentCAlgHom_T_neg_one (k := k)]
    exact h
  have hGK (l : Fin m) := eq_of_toLaurent_eq_T_one_mul_invert (hrel l)
  have hval (a : A) (l : Fin m) : ev a (G l) = (K l).coeff 0 * a + (K l).coeff 1 := by
    conv_lhs => rw [hGK l]
    simp only [ev, map_add, map_mul, Polynomial.aevalTower_X, Polynomial.aevalTower_C,
      AlgHom.id_apply]
  have hy : coordinatePairing e e' P x y = fun l => (K l).coeff 0 := by
    have h := hevK 0
    rw [zero_smul, add_zero] at h
    rw [h]
    funext l
    exact aevalTower_id_zero _
  have hy' : coordinatePairing e e' P x y' = fun l => (K l).coeff 1 := by
    have h := hevG 0
    rw [zero_smul, zero_add] at h
    rw [h]
    funext l
    rw [hval 0 l, mul_zero, zero_add]
  have hsum := hevG 1
  rw [one_smul] at hsum
  rw [hsum, hy, hy']
  funext l
  rw [hval 1 l, Pi.add_apply, mul_one]

/-- **Bilinearity from scalar linearity.** A pairing that is linear over every coefficient
algebra in each argument, in natural coordinates, is bilinear on every test scheme. -/
theorem isBilinearVectorPairing_of_smul (he : IsNaturalVectorCoordinates e)
    (he' : IsNaturalVectorCoordinates e')
    (hsmul_left : ∀ (A : Type u) [CommRing A] [Algebra k A] (r : A) (x y : Fin d → A),
      coordinatePairing e e' P (r • x) y = r • coordinatePairing e e' P x y)
    (hsmul_right : ∀ (A : Type u) [CommRing A] [Algebra k A] (r : A) (x y : Fin d → A),
      coordinatePairing e e' P x (r • y) = r • coordinatePairing e e' P x y) :
    IsBilinearVectorPairing e e' P := by
  intro T x x' y y' r
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [coordinatePairing_global he he', coordinatePairing_global he he',
      coordinatePairing_global he he', map_mul, toAdd_mul]
    exact coordinatePairing_add_left (A := ((algΓ (CommRingCat.of k)).obj T).unop) he he'
      hsmul_left _ _ _
  · rw [coordinatePairing_global he he', coordinatePairing_global he he',
      coordinatePairing_global he he', map_mul, toAdd_mul]
    exact coordinatePairing_add_right (A := ((algΓ (CommRingCat.of k)).obj T).unop) he he'
      hsmul_right _ _ _
  · rw [coordinatePairing_global he he', coordinatePairing_global he he',
      MulEquiv.apply_symm_apply, toAdd_ofAdd]
    exact hsmul_left ((algΓ (CommRingCat.of k)).obj T).unop r _ _
  · rw [coordinatePairing_global he he', coordinatePairing_global he he',
      MulEquiv.apply_symm_apply, toAdd_ofAdd]
    exact hsmul_right ((algΓ (CommRingCat.of k)).obj T).unop r _ _

end Additivity

section Heisenberg

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G U U₂ : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} {a : characterLattice S}
    {j : U ⟶ G} {hj : (subgroup i a).IsRepresentedBy j}
    {j₂ : U₂ ⟶ G} {hj₂ : (subgroup i (2 • a)).IsRepresentedBy j₂}

/-- A Heisenberg normal form of a multipliable relative root group. It consists of an
equivariant section `sec` of schemes of the quotient by the doubled root group, normalized at
the identity, and the cocycle of the group law in it:
`sec(x) sec(y) = cocycle(x, y) sec(x y)`. -/
structure HeisenbergNormalForm (C : DoubleRootCommutatorPairing i a hj hj₂) where
  /-- The inclusion of the doubled root group into the root group. -/
  inclusion : U₂ ⟶ U
  inclusion_comp : inclusion ≫ j = j₂
  range_inclusion : SubgroupFunctor.range inclusion = SubgroupFunctor.range (kernelι C.q)
  /-- The equivariant section of schemes. -/
  sec : C.V.X ⟶ U.X
  sec_comp : sec ≫ C.q.hom.hom = 𝟙 C.V.X
  one_sec : ∀ (T : Over (Spec (CommRingCat.of k))), (1 : T ⟶ C.V.X) ≫ sec = 1
  act_sec : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x : T ⟶ C.V.X),
    (subgroupAction i a j hj).act s (x ≫ sec) = C.action.act s x ≫ sec
  /-- The cocycle of the group law in the section, with values in the doubled root group. -/
  cocycle : C.V.X ⊗ C.V.X ⟶ U₂.X
  sec_mul : ∀ (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ C.V.X),
    (x ≫ sec) * (y ≫ sec) = ((lift x y ≫ cocycle) ≫ inclusion.hom.hom) * ((x * y) ≫ sec)

namespace HeisenbergNormalForm

variable {C : DoubleRootCommutatorPairing i a hj hj₂} (N : HeisenbergNormalForm C)

theorem inclusion_comp_hom : N.inclusion.hom.hom ≫ j.hom.hom = j₂.hom.hom :=
  congrArg (fun f => f.hom.hom) N.inclusion_comp

/-- The inclusion is a monomorphism of schemes. -/
theorem mono_inclusion : Mono N.inclusion.hom.hom := by
  let : Mono j₂.hom.hom := hj₂.1
  exact mono_of_mono_fac N.inclusion_comp_hom

/-- The inclusion intertwines the conjugation actions of the torus. -/
theorem act_inclusion {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ S.X) (w : T ⟶ U₂.X) :
    (subgroupAction i a j hj).act s (w ≫ N.inclusion.hom.hom) =
      (subgroupAction i (2 • a) j₂ hj₂).act s w ≫ N.inclusion.hom.hom := by
  let : Mono j.hom.hom := hj.1
  apply (cancel_mono j.hom.hom).mp
  rw [subgroupAction_act_comp, Category.assoc, Category.assoc, N.inclusion_comp_hom,
    subgroupAction_act_comp]

/-- The cocycle in terms of the section. -/
theorem cocycle_comp {T : Over (Spec (CommRingCat.of k))} (x y : T ⟶ C.V.X) :
    (lift x y ≫ N.cocycle) ≫ N.inclusion.hom.hom =
      (x ≫ N.sec) * (y ≫ N.sec) * ((x * y) ≫ N.sec)⁻¹ := by
  rw [N.sec_mul]
  group

theorem cocycle_one_left {T : Over (Spec (CommRingCat.of k))} (y : T ⟶ C.V.X) :
    lift 1 y ≫ N.cocycle = 1 := by
  let := N.mono_inclusion
  apply (cancel_mono N.inclusion.hom.hom).mp
  rw [N.cocycle_comp, one_mul, N.one_sec, one_mul, mul_inv_cancel, MonObj.one_comp]

theorem cocycle_one_right {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ C.V.X) :
    lift x 1 ≫ N.cocycle = 1 := by
  let := N.mono_inclusion
  apply (cancel_mono N.inclusion.hom.hom).mp
  rw [N.cocycle_comp, mul_one, N.one_sec, mul_one, mul_inv_cancel, MonObj.one_comp]

/-- The cocycle intertwines the torus actions of weights `a` and `2 • a`. -/
theorem cocycle_act {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ S.X) (x y : T ⟶ C.V.X) :
    lift (C.action.act s x) (C.action.act s y) ≫ N.cocycle =
      (subgroupAction i (2 • a) j₂ hj₂).act s (lift x y ≫ N.cocycle) := by
  let := N.mono_inclusion
  apply (cancel_mono N.inclusion.hom.hom).mp
  rw [← N.act_inclusion, N.cocycle_comp, N.cocycle_comp, AutomorphicAction.act_mul_right,
    AutomorphicAction.act_mul_right, AutomorphicAction.act_inv, N.act_sec, N.act_sec,
    N.act_sec, AutomorphicAction.act_mul_right]

/-- The commutator pairing is the antisymmetrization of the cocycle. -/
theorem pairing_eq {T : Over (Spec (CommRingCat.of k))} (x y : T ⟶ C.V.X) :
    lift x y ≫ C.pairing = (lift x y ≫ N.cocycle) * (lift y x ≫ N.cocycle)⁻¹ := by
  let : Mono j₂.hom.hom := hj₂.1
  apply (cancel_mono j₂.hom.hom).mp
  have hq (z : T ⟶ C.V.X) : (z ≫ N.sec) ≫ C.q.hom.hom = z := by
    rw [Category.assoc, N.sec_comp, Category.comp_id]
  have hp := C.lift_pairing T (x ≫ N.sec) (y ≫ N.sec)
  rw [hq, hq] at hp
  have hcomm : y * x = x * y :=
    (commute_of_hasUniqueWeightVectorStructure C.weightVectorStructure T x y).eq.symm
  have hgh := N.sec_mul T x y
  have hhg := N.sec_mul T y x
  rw [hcomm] at hhg
  have hc : (x ≫ N.sec) * (y ≫ N.sec) * (x ≫ N.sec)⁻¹ * (y ≫ N.sec)⁻¹ =
      ((lift x y ≫ N.cocycle) ≫ N.inclusion.hom.hom) *
        ((lift y x ≫ N.cocycle) ≫ N.inclusion.hom.hom)⁻¹ := by
    calc (x ≫ N.sec) * (y ≫ N.sec) * (x ≫ N.sec)⁻¹ * (y ≫ N.sec)⁻¹
        = ((x ≫ N.sec) * (y ≫ N.sec)) * ((y ≫ N.sec) * (x ≫ N.sec))⁻¹ := by group
      _ = _ := by rw [hgh, hhg]; group
  have hj' : ((x ≫ N.sec) * (y ≫ N.sec) * (x ≫ N.sec)⁻¹ * (y ≫ N.sec)⁻¹) ≫ j.hom.hom =
      ((x ≫ N.sec) ≫ j.hom.hom) * ((y ≫ N.sec) ≫ j.hom.hom) * ((x ≫ N.sec) ≫ j.hom.hom)⁻¹ *
        ((y ≫ N.sec) ≫ j.hom.hom)⁻¹ := by
    simp only [MonObj.mul_comp, GrpObj.inv_comp]
  rw [hp, ← hj', hc]
  simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, N.inclusion_comp_hom]


/-- Every point of the root group is a point of the doubled root group times the section at
its image. -/
theorem exists_eq_mul_sec {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ U.X) :
    ∃ w : T ⟶ U₂.X, g = (w ≫ N.inclusion.hom.hom) * ((g ≫ C.q.hom.hom) ≫ N.sec) := by
  have hmem : g * ((g ≫ C.q.hom.hom) ≫ N.sec)⁻¹ ∈
      (SubgroupFunctor.range N.inclusion).carrier T := by
    rw [N.range_inclusion, mem_range_kernelι_iff, MonObj.mul_comp, GrpObj.inv_comp,
      Category.assoc, N.sec_comp, Category.comp_id, mul_inv_cancel]
  obtain ⟨w, hw⟩ := hmem
  refine ⟨w, ?_⟩
  change w ≫ N.inclusion.hom.hom = _ at hw
  rw [hw]
  group

/-- **Bilinearity of the cocycle.** In weight vector coordinates of weight `a` on the quotient
and `2 • a` on the doubled root group, the cocycle is bilinear on every test scheme. -/
theorem isBilinearVectorPairing_cocycle (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0) {d m : ℕ}
    {e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ C.V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤))}
    {e' : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ U₂.X) ≃* Multiplicative (Fin m → Γ(T.left, ⊤))}
    (he : IsWeightVectorCoordinates C.action a e)
    (he' : IsWeightVectorCoordinates (subgroupAction i (2 • a) j₂ hj₂) (2 • a) e') :
    IsBilinearVectorPairing e e' N.cocycle :=
  isBilinearVectorPairing_of_smul he.1 he'.1
    (fun _ _ _ r x y => (coordinatePairing_smul hS ha he he' (fun _ s x y => N.cocycle_act s x y)
      (fun _ y => N.cocycle_one_left y) (fun _ x => N.cocycle_one_right x) r x y).1)
    (fun _ _ _ r x y => (coordinatePairing_smul hS ha he he' (fun _ s x y => N.cocycle_act s x y)
      (fun _ y => N.cocycle_one_left y) (fun _ x => N.cocycle_one_right x) r x y).2)

end HeisenbergNormalForm

/-- **Existence of the Heisenberg normal form** of a multipliable relative root group whose
higher multiples `n • a`, `n ≥ 3`, are not relative roots, for an affine representative of the
root group. -/
theorem nonempty_heisenbergNormalForm [IsAffineHom G.X.hom] [Smooth G.X.hom]
    [IsAffineHom U.X.hom] (C : DoubleRootCommutatorPairing i a hj hj₂)
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i) :
    Nonempty (HeisenbergNormalForm C) := by
  let : Mono j.hom.hom := hj.1
  have hle : subgroup i (2 • a) ≤ subgroup i a :=
    double_subgroup_le_of_cyclicComparison cyclicRootFunctorComparison inferInstance hS i ha
  let n := hj.factorHom j₂ (by rw [hj₂.2]; exact hle)
  have hκ' := SubgroupFunctor.IsRepresentedBy.factor hj hj₂ hle
  have hn_comp : n ≫ j = j₂ := hj.factorHom_comp j₂ _
  let : Mono n.hom.hom := hκ'.1
  have hrange : SubgroupFunctor.range n = SubgroupFunctor.range (kernelι C.q) :=
    hκ'.2.trans C.isFppfQuotient.2.2.2.symm
  obtain ⟨d, e, he⟩ := C.weightVectorStructure.1
  have h2a : 2 • a ≠ 0 := hS.nsmul_ne_zero ha (by omega)
  obtain ⟨m, e', he'⟩ := weightVectorCoordinatesOfNoHigherRoots hS i h2a
    (hasNoHigherRoots_two_nsmul hhigh) hj₂
  have hV₂ : IsVectorGroupOfDimension U₂ m := ⟨e', he'.1⟩
  let : IsAffineHom C.V.X.hom := IsVectorGroupOfDimension.isAffineHom ⟨e, he.1⟩
  let : IsAffineHom U₂.X.hom := hV₂.isAffineHom
  let : Flat C.q.hom.hom.left := C.isFppfQuotient.1
  let : Surjective C.q.hom.hom.left := C.isFppfQuotient.2.1
  obtain ⟨s₀, hs₀⟩ := IsVectorGroupOfDimension.exists_quotientSection n C.q hrange hV₂
  have hker : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ U.X),
      g ∈ (SubgroupFunctor.range n).carrier T ↔ g ≫ C.q.hom.hom = 1 := by
    intro T g
    rw [hrange, mem_range_kernelι_iff]
  have hq : ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ S.X) (g : T ⟶ U.X),
      (subgroupAction i a j hj).act t g ≫ C.q.hom.hom =
        C.action.act t (g ≫ C.q.hom.hom) :=
    fun T t g => (C.act_comp T t g).symm
  have hκj : n.hom.hom ≫ j.hom.hom = j₂.hom.hom := congrArg (fun f => f.hom.hom) hn_comp
  have hi : ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ S.X) (w : T ⟶ U₂.X),
      (subgroupAction i a j hj).act t (w ≫ n.hom.hom) =
        (subgroupAction i (2 • a) j₂ hj₂).act t w ≫ n.hom.hom := by
    intro T t w
    apply (cancel_mono j.hom.hom).mp
    rw [subgroupAction_act_comp, Category.assoc, Category.assoc, hκj, subgroupAction_act_comp]
  have he'lin : IsLinearVectorCoordinates (subgroupAction i (2 • a) j₂ hj₂) e' := by
    refine ⟨he'.1, fun T h c v => ?_⟩
    rw [he'.2, MulEquiv.apply_symm_apply, toAdd_ofAdd, he'.2, smul_comm]
  obtain ⟨σ, hσ, hσact⟩ := IsSplitTorus.exists_equivariantSection hS
    (subgroupAction i a j hj) C.action (subgroupAction i (2 • a) j₂ hj₂) n C.q hker hq hi
    s₀ hs₀ e' he'lin
  -- normalize the section at the identity
  let σ' : C.V.X ⟶ U.X := σ * ((1 : C.V.X ⟶ C.V.X) ≫ σ)⁻¹
  have hσ'pt (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ C.V.X) :
      x ≫ σ' = (x ≫ σ) * ((1 : T ⟶ C.V.X) ≫ σ)⁻¹ := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, MonObj.comp_one]
  have hσ'q : σ' ≫ C.q.hom.hom = 𝟙 C.V.X := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hσ, Category.assoc, hσ, Category.comp_id, inv_one,
      mul_one]
  have hσ'one (T : Over (Spec (CommRingCat.of k))) : (1 : T ⟶ C.V.X) ≫ σ' = 1 := by
    rw [hσ'pt, mul_inv_cancel]
  have hσ'act (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x : T ⟶ C.V.X) :
      (subgroupAction i a j hj).act s (x ≫ σ') = C.action.act s x ≫ σ' := by
    rw [hσ'pt, hσ'pt, AutomorphicAction.act_mul_right, AutomorphicAction.act_inv, hσact, hσact,
      AutomorphicAction.act_one]
  -- the cocycle on the universal pair
  let D : C.V.X ⊗ C.V.X ⟶ U.X :=
    (fst C.V.X C.V.X ≫ σ') * (snd C.V.X C.V.X ≫ σ') * ((fst C.V.X C.V.X * snd C.V.X C.V.X) ≫ σ')⁻¹
  have hD : D ∈ (SubgroupFunctor.range n).carrier (C.V.X ⊗ C.V.X) := by
    rw [hker]
    simp only [D, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hσ'q, Category.comp_id,
      mul_inv_cancel]
  let β : C.V.X ⊗ C.V.X ⟶ U₂.X := Classical.choose hD
  have hβ : β ≫ n.hom.hom = D := Classical.choose_spec hD
  refine ⟨{
    inclusion := n
    inclusion_comp := hn_comp
    range_inclusion := hrange
    sec := σ'
    sec_comp := hσ'q
    one_sec := hσ'one
    act_sec := hσ'act
    cocycle := β
    sec_mul := fun T x y => ?_ }⟩
  have hβ' : (lift x y ≫ β) ≫ n.hom.hom = (x ≫ σ') * (y ≫ σ') * ((x * y) ≫ σ')⁻¹ := by
    rw [Category.assoc, hβ]
    simp only [D, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, lift_fst, lift_snd]
  rw [hβ']
  group

/-- A chosen Heisenberg normal form. -/
def heisenbergNormalForm [IsAffineHom G.X.hom] [Smooth G.X.hom] [IsAffineHom U.X.hom]
    (C : DoubleRootCommutatorPairing i a hj hj₂) (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i) : HeisenbergNormalForm C :=
  Classical.choice (nonempty_heisenbergNormalForm C hS ha hhigh)

end Heisenberg

end Langlands.GroupScheme.RelativeRoot
