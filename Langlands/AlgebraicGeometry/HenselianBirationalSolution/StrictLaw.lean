import Langlands.AlgebraicGeometry.BirationalGroupLaw
import Langlands.AlgebraicGeometry.HenselianBirationalSolution.Density

/-! # The law of a birational group law on points

For a representative `m : BirationalGroupLaw g` of a birational group law on `g : Y ⟶ S` and
`T`-valued points `x`, `y` of `Y` with `(x, y)` in the domain of `m`, `m.mulPt x y` is the
`T`-valued point `x y`. The universal translations being monomorphisms gives left and right
cancellation; points of their images give left and right division. The predicate
`IsStrictDomain` says that the domain and the images of both universal translations are dense in
the fibres of both projections of `Y ×_S Y`.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

variable {S Y : Scheme.{u}} {g : Y ⟶ S} (m : BirationalGroupLaw g)

/-- The universal left translation `(x, y) ↦ (x, x y)` of `m`. -/
abbrev leftT : m.domain.toScheme ⟶ pullback g g := leftTranslation g m.domain m.mul m.mul_comp

/-- The universal right translation `(x, y) ↦ (x y, y)` of `m`. -/
abbrev rightT : m.domain.toScheme ⟶ pullback g g := rightTranslation g m.domain m.mul m.mul_comp

instance : IsOpenImmersion (leftT m) := m.isOpenImmersion_leftTranslation
instance : IsOpenImmersion (rightT m) := m.isOpenImmersion_rightTranslation

/-- The domain of `m` and the images of both universal translations are dense in the fibres of
both projections `Y ×_S Y ⟶ Y`. -/
structure IsStrictDomain : Prop where
  domain_fst : FibreGenerizationDense (pullback.fst g g) (m.domain : Set ↥(pullback g g))
  domain_snd : FibreGenerizationDense (pullback.snd g g) (m.domain : Set ↥(pullback g g))
  left_fst : FibreGenerizationDense (pullback.fst g g) (Set.range (leftT m))
  left_snd : FibreGenerizationDense (pullback.snd g g) (Set.range (leftT m))
  right_fst : FibreGenerizationDense (pullback.fst g g) (Set.range (rightT m))
  right_snd : FibreGenerizationDense (pullback.snd g g) (Set.range (rightT m))

variable {m}

section Points

variable {T : Scheme.{u}}

/-- The pair `(x, y) : T ⟶ Y ×_S Y` lies in a set of points. -/
abbrev PairIn (x y : T ⟶ Y) (h : x ≫ g = y ≫ g) (A : Set ↥(pullback g g)) : Prop :=
  Set.range (pullback.lift x y h) ⊆ A

theorem PairIn.comp {x y : T ⟶ Y} {h : x ≫ g = y ≫ g} {A : Set ↥(pullback g g)}
    (hA : PairIn x y h A) {T' : Scheme.{u}} (φ : T' ⟶ T) :
    PairIn (φ ≫ x) (φ ≫ y) (by rw [Category.assoc, h, Category.assoc]) A := by
  have he : pullback.lift (φ ≫ x) (φ ≫ y) (by rw [Category.assoc, h, Category.assoc]) =
      φ ≫ pullback.lift x y h := by
    apply pullback.hom_ext <;> simp
  rintro _ ⟨t, rfl⟩
  refine hA ⟨φ t, ?_⟩
  rw [he, Scheme.Hom.comp_apply]

theorem PairIn.mono {x y : T ⟶ Y} {h : x ≫ g = y ≫ g} {A B : Set ↥(pullback g g)}
    (hA : PairIn x y h A) (hAB : A ⊆ B) : PairIn x y h B :=
  hA.trans hAB

theorem PairIn.of_eq {x y x' y' : T ⟶ Y} {h : x ≫ g = y ≫ g} {A : Set ↥(pullback g g)}
    (hA : PairIn x y h A) (hx : x = x') (hy : y = y') {h' : x' ≫ g = y' ≫ g} :
    PairIn x' y' h' A := by
  subst hx hy
  exact hA

end Points

end Langlands.AlgebraicGeometry.HenselianBirationalSolution

namespace Langlands.AlgebraicGeometry.BirationalGroupLaw

open Langlands.AlgebraicGeometry.HenselianBirationalSolution

variable {S Y : Scheme.{u}} {g : Y ⟶ S} (m : BirationalGroupLaw g)

section Points

variable {T : Scheme.{u}}

/-- `(x, y)` lies in the domain of `m`. -/
abbrev Defined (x y : T ⟶ Y) (h : x ≫ g = y ≫ g) : Prop := PairIn x y h m.domain

/-- The lift of a pair in the domain of `m` to the domain. -/
def liftDom (x y : T ⟶ Y) (h : x ≫ g = y ≫ g) (hd : m.Defined x y h) : T ⟶ m.domain.toScheme :=
  IsOpenImmersion.lift m.domain.ι (pullback.lift x y h) (by rwa [Scheme.Opens.range_ι])

@[reassoc (attr := simp)]
theorem liftDom_ι (x y : T ⟶ Y) (h : x ≫ g = y ≫ g) (hd : m.Defined x y h) :
    m.liftDom x y h hd ≫ m.domain.ι = pullback.lift x y h :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
theorem liftDom_fst (x y : T ⟶ Y) (h : x ≫ g = y ≫ g) (hd : m.Defined x y h) :
    m.liftDom x y h hd ≫ m.domain.ι ≫ pullback.fst g g = x := by
  rw [liftDom_ι_assoc, pullback.lift_fst]

@[reassoc (attr := simp)]
theorem liftDom_snd (x y : T ⟶ Y) (h : x ≫ g = y ≫ g) (hd : m.Defined x y h) :
    m.liftDom x y h hd ≫ m.domain.ι ≫ pullback.snd g g = y := by
  rw [liftDom_ι_assoc, pullback.lift_snd]

theorem liftDom_eq (x y : T ⟶ Y) (h : x ≫ g = y ≫ g) (hd : m.Defined x y h)
    (a : T ⟶ m.domain.toScheme) (ha₁ : a ≫ m.domain.ι ≫ pullback.fst g g = x)
    (ha₂ : a ≫ m.domain.ι ≫ pullback.snd g g = y) : a = m.liftDom x y h hd := by
  rw [← cancel_mono m.domain.ι, liftDom_ι]
  apply pullback.hom_ext <;> simpa

/-- The product `x y` of two `T`-points with `(x, y)` in the domain of `m`. -/
def mulPt (x y : T ⟶ Y) (h : x ≫ g = y ≫ g) (hd : m.Defined x y h) : T ⟶ Y :=
  m.liftDom x y h hd ≫ m.mul

@[reassoc (attr := simp)]
theorem mulPt_comp_g (x y : T ⟶ Y) (h : x ≫ g = y ≫ g) (hd : m.Defined x y h) :
    m.mulPt x y h hd ≫ g = x ≫ g := by
  rw [mulPt, Category.assoc, m.mul_comp, liftDom_fst_assoc]

theorem comp_liftDom (x y : T ⟶ Y) (h : x ≫ g = y ≫ g) (hd : m.Defined x y h)
    {T' : Scheme.{u}} (φ : T' ⟶ T) :
    φ ≫ m.liftDom x y h hd = m.liftDom (φ ≫ x) (φ ≫ y)
      (by rw [Category.assoc, h, Category.assoc]) (hd.comp φ) := by
  apply liftDom_eq <;> simp

theorem comp_mulPt (x y : T ⟶ Y) (h : x ≫ g = y ≫ g) (hd : m.Defined x y h)
    {T' : Scheme.{u}} (φ : T' ⟶ T) :
    φ ≫ m.mulPt x y h hd = m.mulPt (φ ≫ x) (φ ≫ y)
      (by rw [Category.assoc, h, Category.assoc]) (hd.comp φ) := by
  rw [mulPt, ← Category.assoc, comp_liftDom, mulPt]

/-- Proof-irrelevant congruence for `mulPt`. -/
theorem mulPt_congr {x y x' y' : T ⟶ Y} (hx : x = x') (hy : y = y') {h : x ≫ g = y ≫ g}
    {h' : x' ≫ g = y' ≫ g} {hd : m.Defined x y h} {hd' : m.Defined x' y' h'} :
    m.mulPt x y h hd = m.mulPt x' y' h' hd' := by
  subst hx hy
  rfl

/-- Associativity of `m` on points: `(x y) z = x (y z)` whenever both sides are defined. -/
theorem mulPt_assoc (x y z : T ⟶ Y) (hxy : x ≫ g = y ≫ g) (hyz : y ≫ g = z ≫ g)
    (dxy : m.Defined x y hxy) (dyz : m.Defined y z hyz)
    (dl : m.Defined (m.mulPt x y hxy dxy) z (by simp [hxy, hyz]))
    (dr : m.Defined x (m.mulPt y z hyz dyz) (by simp [hxy])) :
    m.mulPt (m.mulPt x y hxy dxy) z (by simp [hxy, hyz]) dl =
      m.mulPt x (m.mulPt y z hyz dyz) (by simp [hxy]) dr := by
  apply m.assoc T (m.liftDom x y hxy dxy) _ (m.liftDom y z hyz dyz) _ <;> simp [mulPt]

/-- The universal left translation on points. -/
theorem liftDom_leftT (x y : T ⟶ Y) (h : x ≫ g = y ≫ g) (hd : m.Defined x y h) :
    m.liftDom x y h hd ≫ leftT m =
      pullback.lift x (m.mulPt x y h hd) (by simp [h]) := by
  apply pullback.hom_ext
  · simp [leftTranslation]
  · simp [leftTranslation, mulPt]

/-- The universal right translation on points. -/
theorem liftDom_rightT (x y : T ⟶ Y) (h : x ≫ g = y ≫ g) (hd : m.Defined x y h) :
    m.liftDom x y h hd ≫ rightT m =
      pullback.lift (m.mulPt x y h hd) y (by simp [h]) := by
  apply pullback.hom_ext
  · simp [rightTranslation, mulPt]
  · simp [rightTranslation]

/-- Left cancellation: `x y = x y'` implies `y = y'`. -/
theorem mulPt_left_cancel {x y y' : T ⟶ Y} {h : x ≫ g = y ≫ g} {h' : x ≫ g = y' ≫ g}
    {hd : m.Defined x y h} {hd' : m.Defined x y' h'}
    (he : m.mulPt x y h hd = m.mulPt x y' h' hd') : y = y' := by
  have : m.liftDom x y h hd = m.liftDom x y' h' hd' := by
    rw [← cancel_mono (leftT m), liftDom_leftT, liftDom_leftT]
    apply pullback.hom_ext <;> simp [he]
  rw [← m.liftDom_snd x y h hd, this, liftDom_snd]

/-- Right cancellation: `x y = x' y` implies `x = x'`. -/
theorem mulPt_right_cancel {x x' y : T ⟶ Y} {h : x ≫ g = y ≫ g} {h' : x' ≫ g = y ≫ g}
    {hd : m.Defined x y h} {hd' : m.Defined x' y h'}
    (he : m.mulPt x y h hd = m.mulPt x' y h' hd') : x = x' := by
  have : m.liftDom x y h hd = m.liftDom x' y h' hd' := by
    rw [← cancel_mono (rightT m), liftDom_rightT, liftDom_rightT]
    apply pullback.hom_ext <;> simp [he]
  rw [← m.liftDom_fst x y h hd, this, liftDom_fst]

/-- Right cancellation with propositionally equal right factors. -/
theorem mulPt_right_cancel' {x x' y y' : T ⟶ Y} (hy : y = y') {h : x ≫ g = y ≫ g}
    {h' : x' ≫ g = y' ≫ g} {hd : m.Defined x y h} {hd' : m.Defined x' y' h'}
    (he : m.mulPt x y h hd = m.mulPt x' y' h' hd') : x = x' := by
  subst hy
  exact m.mulPt_right_cancel he

/-- Left cancellation with propositionally equal left factors. -/
theorem mulPt_left_cancel' {x x' y y' : T ⟶ Y} (hx : x = x') {h : x ≫ g = y ≫ g}
    {h' : x' ≫ g = y' ≫ g} {hd : m.Defined x y h} {hd' : m.Defined x' y' h'}
    (he : m.mulPt x y h hd = m.mulPt x' y' h' hd') : y = y' := by
  subst hx
  exact m.mulPt_left_cancel he

/-- Left division `w⁻¹ z` for `(w, z)` in the image of the universal left translation. -/
def ldiv (w z : T ⟶ Y) (h : w ≫ g = z ≫ g) (hV : PairIn w z h (Set.range (leftT m))) :
    T ⟶ Y :=
  IsOpenImmersion.lift (leftT m) (pullback.lift w z h) hV ≫ m.domain.ι ≫ pullback.snd g g

theorem leftT_snd : leftT m ≫ pullback.snd g g = m.mul := pullback.lift_snd _ _ _

theorem leftT_fst : leftT m ≫ pullback.fst g g = m.domain.ι ≫ pullback.fst g g :=
  pullback.lift_fst _ _ _

theorem rightT_fst : rightT m ≫ pullback.fst g g = m.mul := pullback.lift_fst _ _ _

theorem rightT_snd : rightT m ≫ pullback.snd g g = m.domain.ι ≫ pullback.snd g g :=
  pullback.lift_snd _ _ _

/-- A morphism to `Y ×_S Y` lands in the domain when it factors through the domain. -/
theorem pairIn_domain_of_eq {x y : T ⟶ Y} {h : x ≫ g = y ≫ g} (a : T ⟶ m.domain.toScheme)
    (ha : pullback.lift x y h = a ≫ m.domain.ι) : m.Defined x y h := by
  rintro _ ⟨t, rfl⟩
  rw [ha, Scheme.Hom.comp_apply]
  exact (a t).2

/-- A morphism to `Y ×_S Y` lands in the range of a morphism through which it factors. -/
theorem pairIn_range_of_eq {x y : T ⟶ Y} {h : x ≫ g = y ≫ g} {Z : Scheme.{u}}
    (e : Z ⟶ pullback g g) (a : T ⟶ Z) (ha : pullback.lift x y h = a ≫ e) :
    PairIn x y h (Set.range e) := by
  rintro _ ⟨t, rfl⟩
  rw [ha, Scheme.Hom.comp_apply]
  exact ⟨a t, rfl⟩

theorem pairIn_leftT (x y : T ⟶ Y) (h : x ≫ g = y ≫ g) (hd : m.Defined x y h) :
    PairIn x (m.mulPt x y h hd) (by simp [h]) (Set.range (leftT m)) :=
  pairIn_range_of_eq _ _ (m.liftDom_leftT x y h hd).symm

theorem pairIn_rightT (x y : T ⟶ Y) (h : x ≫ g = y ≫ g) (hd : m.Defined x y h) :
    PairIn (m.mulPt x y h hd) y (by simp [h]) (Set.range (rightT m)) :=
  pairIn_range_of_eq _ _ (m.liftDom_rightT x y h hd).symm

theorem ldiv_comp_g (w z : T ⟶ Y) (h : w ≫ g = z ≫ g)
    (hV : PairIn w z h (Set.range (leftT m))) : w ≫ g = m.ldiv w z h hV ≫ g := by
  set a := IsOpenImmersion.lift (leftT m) (pullback.lift w z h) hV
  have hfac : a ≫ leftT m = pullback.lift w z h := IsOpenImmersion.lift_fac _ _ _
  have ha₁ : a ≫ m.domain.ι ≫ pullback.fst g g = w := by
    rw [← leftT_fst, ← Category.assoc, hfac, pullback.lift_fst]
  calc w ≫ g = (a ≫ m.domain.ι ≫ pullback.fst g g) ≫ g := by rw [ha₁]
    _ = m.ldiv w z h hV ≫ g := by
      simp only [ldiv, Category.assoc, pullback.condition]
      rfl

theorem ldiv_spec (w z : T ⟶ Y) (h : w ≫ g = z ≫ g)
    (hV : PairIn w z h (Set.range (leftT m))) :
    ∃ hd : m.Defined w (m.ldiv w z h hV) (m.ldiv_comp_g w z h hV),
      m.mulPt w (m.ldiv w z h hV) (m.ldiv_comp_g w z h hV) hd = z := by
  set a := IsOpenImmersion.lift (leftT m) (pullback.lift w z h) hV
  have hfac : a ≫ leftT m = pullback.lift w z h := IsOpenImmersion.lift_fac _ _ _
  have ha₁ : a ≫ m.domain.ι ≫ pullback.fst g g = w := by
    rw [← leftT_fst, ← Category.assoc, hfac, pullback.lift_fst]
  have ha₂ : a ≫ m.domain.ι ≫ pullback.snd g g = m.ldiv w z h hV := rfl
  have hpair : pullback.lift w (m.ldiv w z h hV) (m.ldiv_comp_g w z h hV) =
      a ≫ m.domain.ι := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, ha₁]
    · rw [pullback.lift_snd, Category.assoc, ha₂]
  have hd := m.pairIn_domain_of_eq a hpair
  refine ⟨hd, ?_⟩
  have hla : m.liftDom w (m.ldiv w z h hV) (m.ldiv_comp_g w z h hV) hd = a :=
    (m.liftDom_eq _ _ _ hd a ha₁ ha₂).symm
  rw [mulPt, hla, ← leftT_snd, ← Category.assoc, hfac, pullback.lift_snd]

/-- Left division is the unique solution of `w y = z`. -/
theorem ldiv_eq (w y : T ⟶ Y) (h : w ≫ g = y ≫ g) (hd : m.Defined w y h) :
    m.ldiv w (m.mulPt w y h hd) (by simp [h]) (m.pairIn_leftT w y h hd) = y := by
  have hl : IsOpenImmersion.lift (leftT m) (pullback.lift w (m.mulPt w y h hd) (by simp [h]))
      (m.pairIn_leftT w y h hd) = m.liftDom w y h hd :=
    (IsOpenImmersion.lift_uniq _ _ _ _ (m.liftDom_leftT w y h hd)).symm
  rw [ldiv, hl, liftDom_snd]

/-- Right division `z y⁻¹` for `(z, y)` in the image of the universal right translation. -/
def rdiv (z y : T ⟶ Y) (h : z ≫ g = y ≫ g) (hW : PairIn z y h (Set.range (rightT m))) :
    T ⟶ Y :=
  IsOpenImmersion.lift (rightT m) (pullback.lift z y h) hW ≫ m.domain.ι ≫ pullback.fst g g

theorem rdiv_comp_g (z y : T ⟶ Y) (h : z ≫ g = y ≫ g)
    (hW : PairIn z y h (Set.range (rightT m))) : m.rdiv z y h hW ≫ g = y ≫ g := by
  set a := IsOpenImmersion.lift (rightT m) (pullback.lift z y h) hW
  have hfac : a ≫ rightT m = pullback.lift z y h := IsOpenImmersion.lift_fac _ _ _
  have ha₂ : a ≫ m.domain.ι ≫ pullback.snd g g = y := by
    rw [← rightT_snd, ← Category.assoc, hfac, pullback.lift_snd]
  calc m.rdiv z y h hW ≫ g = (a ≫ m.domain.ι ≫ pullback.snd g g) ≫ g := by
        simp only [rdiv, Category.assoc, pullback.condition]
        rfl
    _ = y ≫ g := by rw [ha₂]

theorem rdiv_spec (z y : T ⟶ Y) (h : z ≫ g = y ≫ g)
    (hW : PairIn z y h (Set.range (rightT m))) :
    ∃ hd : m.Defined (m.rdiv z y h hW) y (m.rdiv_comp_g z y h hW),
      m.mulPt (m.rdiv z y h hW) y (m.rdiv_comp_g z y h hW) hd = z := by
  set a := IsOpenImmersion.lift (rightT m) (pullback.lift z y h) hW
  have hfac : a ≫ rightT m = pullback.lift z y h := IsOpenImmersion.lift_fac _ _ _
  have ha₂ : a ≫ m.domain.ι ≫ pullback.snd g g = y := by
    rw [← rightT_snd, ← Category.assoc, hfac, pullback.lift_snd]
  have ha₁ : a ≫ m.domain.ι ≫ pullback.fst g g = m.rdiv z y h hW := rfl
  have hpair : pullback.lift (m.rdiv z y h hW) y (m.rdiv_comp_g z y h hW) =
      a ≫ m.domain.ι := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, ha₁]
    · rw [pullback.lift_snd, Category.assoc, ha₂]
  have hd := m.pairIn_domain_of_eq a hpair
  refine ⟨hd, ?_⟩
  have hla : m.liftDom (m.rdiv z y h hW) y (m.rdiv_comp_g z y h hW) hd = a :=
    (m.liftDom_eq _ _ _ hd a ha₁ ha₂).symm
  rw [mulPt, hla, ← rightT_fst, ← Category.assoc, hfac, pullback.lift_fst]

/-- Right division is the unique solution of `x y = z`. -/
theorem rdiv_eq (x y : T ⟶ Y) (h : x ≫ g = y ≫ g) (hd : m.Defined x y h) :
    m.rdiv (m.mulPt x y h hd) y (by simp [h]) (m.pairIn_rightT x y h hd) = x := by
  have hl : IsOpenImmersion.lift (rightT m) (pullback.lift (m.mulPt x y h hd) y (by simp [h]))
      (m.pairIn_rightT x y h hd) = m.liftDom x y h hd :=
    (IsOpenImmersion.lift_uniq _ _ _ _ (m.liftDom_rightT x y h hd)).symm
  rw [rdiv, hl, liftDom_fst]

theorem comp_ldiv (w z : T ⟶ Y) (h : w ≫ g = z ≫ g)
    (hV : PairIn w z h (Set.range (leftT m))) {T' : Scheme.{u}} (φ : T' ⟶ T) :
    φ ≫ m.ldiv w z h hV = m.ldiv (φ ≫ w) (φ ≫ z) (by rw [Category.assoc, h, Category.assoc])
      (hV.comp φ) := by
  simp only [ldiv, ← Category.assoc]
  congr 2
  apply IsOpenImmersion.lift_uniq
  rw [Category.assoc, IsOpenImmersion.lift_fac]
  apply pullback.hom_ext <;> simp

theorem comp_rdiv (z y : T ⟶ Y) (h : z ≫ g = y ≫ g)
    (hW : PairIn z y h (Set.range (rightT m))) {T' : Scheme.{u}} (φ : T' ⟶ T) :
    φ ≫ m.rdiv z y h hW = m.rdiv (φ ≫ z) (φ ≫ y) (by rw [Category.assoc, h, Category.assoc])
      (hW.comp φ) := by
  simp only [rdiv, ← Category.assoc]
  congr 2
  apply IsOpenImmersion.lift_uniq
  rw [Category.assoc, IsOpenImmersion.lift_fac]
  apply pullback.hom_ext <;> simp

end Points

end Langlands.AlgebraicGeometry.BirationalGroupLaw
