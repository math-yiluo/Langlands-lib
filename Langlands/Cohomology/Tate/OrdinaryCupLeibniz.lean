import Langlands.Cohomology.Tate.OrdinaryCupDescent

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory groupCohomology

namespace Langlands.Tate.OrdinaryCup

variable {R G : Type u} [CommRing R] [Group G]
variable (A B C : Rep R G)

/-- Transport actual inhomogeneous cochains along an equality of degrees. -/
def transport {m n : ℕ} (h : m = n) :
    (inhomogeneousCochains C).X m ≃ₗ[R] (inhomogeneousCochains C).X n := by
  subst h
  exact LinearEquiv.refl R _

@[simp]
lemma transport_rfl (n : ℕ) (f : (inhomogeneousCochains C).X n) :
    transport C rfl f = f := rfl

@[simp]
lemma transport_apply {m n : ℕ} (h : m = n)
    (f : (inhomogeneousCochains C).X m) (x : Fin n → G) :
    transport C h f x = f (x ∘ Fin.cast h) := by
  subst h
  rfl

@[simp]
lemma transport_trans {m n k : ℕ} (h : m = n) (h' : n = k)
    (f : (inhomogeneousCochains C).X m) :
    transport C h' (transport C h f) = transport C (h.trans h') f := by
  subst h
  subst h'
  rfl

lemma differential_eq_transport (m n : ℕ) (h : m + 1 = n)
    (f : (inhomogeneousCochains C).X m) :
    (inhomogeneousCochains C).d m n f =
      transport C h (_root_.inhomogeneousCochains.d C m f) := by
  subst n
  rw [groupCohomology.inhomogeneousCochains.d_def]
  rfl

lemma differential_transport_source {i j n : ℕ} (h : i = j)
    (f : (inhomogeneousCochains C).X i) :
    (inhomogeneousCochains C).d i n f =
      (inhomogeneousCochains C).d j n (transport C h f) := by
  subst h
  rfl

variable
  (cp : ∀ p q : ℕ, (inhomogeneousCochains A).X p →ₗ[R]
    (inhomogeneousCochains B).X q →ₗ[R] (inhomogeneousCochains C).X (p + q))
  (leibniz : ∀ p q f g,
    _root_.inhomogeneousCochains.d C (p + q) (cp p q f g) =
      transport C (by omega : (p + 1) + q = (p + q) + 1)
        (cp (p + 1) q (_root_.inhomogeneousCochains.d A p f) g) +
      (-1 : R) ^ p • cp p (q + 1) f (_root_.inhomogeneousCochains.d B q g))

include leibniz in
lemma cycles_of_leibniz (p q : ℕ) (f : (inhomogeneousCochains A).X p)
    (g : (inhomogeneousCochains B).X q)
    (hf : _root_.inhomogeneousCochains.d A p f = 0)
    (hg : _root_.inhomogeneousCochains.d B q g = 0) :
    _root_.inhomogeneousCochains.d C (p + q) (cp p q f g) = 0 := by
  rw [leibniz, hf, hg]
  simp

include leibniz in
lemma boundary_left_of_leibniz (p q : ℕ)
    (a : ((inhomogeneousCochains A).sc p).X₁) (b : cocycles B q) :
    ∃ (i : ℕ) (w : (inhomogeneousCochains C).X i),
      cp p q (((inhomogeneousCochains A).sc p).f a) (iCocycles B q b) =
        (inhomogeneousCochains C).d i (p + q) w := by
  cases p with
  | zero =>
      have hf : ((inhomogeneousCochains A).sc 0).f = 0 := by
        exact (inhomogeneousCochains A).shape _ 0 (by simp)
      refine ⟨0, 0, ?_⟩
      rw [hf]
      simp
  | succ p =>
      let a' := transport A (CochainComplex.prev_nat_succ p) a
      have hf : ((inhomogeneousCochains A).sc (p + 1)).f a =
          _root_.inhomogeneousCochains.d A p a' := by
        change (inhomogeneousCochains A).d _ (p + 1) a = _
        rw [differential_transport_source A (CochainComplex.prev_nat_succ p),
          groupCohomology.inhomogeneousCochains.d_def]
      refine ⟨p + q, cp p q a' (iCocycles B q b), ?_⟩
      rw [hf, differential_eq_transport C (p + q) ((p + 1) + q) (by omega)]
      apply (transport C (by omega : (p + 1) + q = (p + q) + 1)).injective
      rw [transport_trans, transport_rfl]
      have h := leibniz p q a' (iCocycles B q b)
      rw [cocycle_d, map_zero, smul_zero, add_zero] at h
      exact h.symm

include leibniz in
lemma boundary_right_of_leibniz (p q : ℕ)
    (a : cocycles A p) (b : ((inhomogeneousCochains B).sc q).X₁) :
    ∃ (i : ℕ) (w : (inhomogeneousCochains C).X i),
      cp p q (iCocycles A p a) (((inhomogeneousCochains B).sc q).f b) =
        (inhomogeneousCochains C).d i (p + q) w := by
  cases q with
  | zero =>
      have hf : ((inhomogeneousCochains B).sc 0).f = 0 := by
        exact (inhomogeneousCochains B).shape _ 0 (by simp)
      refine ⟨0, 0, ?_⟩
      rw [hf]
      change cp p 0 (iCocycles A p a) 0 = (inhomogeneousCochains C).d 0 (p + 0) 0
      rw [map_zero, map_zero]
  | succ q =>
      let b' := transport B (CochainComplex.prev_nat_succ q) b
      have hf : ((inhomogeneousCochains B).sc (q + 1)).f b =
          _root_.inhomogeneousCochains.d B q b' := by
        change (inhomogeneousCochains B).d _ (q + 1) b = _
        rw [differential_transport_source B (CochainComplex.prev_nat_succ q),
          groupCohomology.inhomogeneousCochains.d_def]
      refine ⟨p + q, (-1 : R) ^ p • cp p q (iCocycles A p a) b', ?_⟩
      rw [hf]
      change cp p (q + 1) (iCocycles A p a) (_root_.inhomogeneousCochains.d B q b') =
        (inhomogeneousCochains C).d (p + q) ((p + q) + 1) _
      rw [groupCohomology.inhomogeneousCochains.d_def, map_smul]
      have hs : (-1 : R) ^ p * (-1 : R) ^ p = 1 := by
        rw [← mul_pow]
        simp
      rw [leibniz, cocycle_d]
      simp [smul_smul, hs]

/-- Internal descent of a cochain pairing with a supplied proved Leibniz identity. -/
def fromLeibniz (p q : ℕ) : groupCohomology A p →ₗ[R]
    groupCohomology B q →ₗ[R] groupCohomology C (p + q) :=
  fromCochains A B C p q (cp p q)
    (cycles_of_leibniz A B C cp leibniz p q)
    (boundary_left_of_leibniz A B C cp leibniz p q)
    (boundary_right_of_leibniz A B C cp leibniz p q)

@[simp]
lemma fromLeibniz_π_π (p q : ℕ) (a : cocycles A p) (b : cocycles B q) :
    fromLeibniz A B C cp leibniz p q (π A p a) (π B q b) =
      π C (p + q) (onCocycles A B C p q (cp p q)
        (cycles_of_leibniz A B C cp leibniz p q) a b) :=
  fromCochains_π_π _ _ _ _ _ _ _ _ _ _ _

end Langlands.Tate.OrdinaryCup
