import Langlands.GroupScheme.Torus.DiagonalizableFixedSmoothStatement
import Langlands.GroupScheme.CorepresentedPoints
import Langlands.GroupScheme.Lie.AffineCoordinates
import Langlands.GroupScheme.Torus.FixedSubgroupSmoothAlgebraBridge

/-! # Smooth fixed subgroups for diagonalizable actions: proof -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry AddMonoidAlgebra
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Diagonalizable.FixedSmooth

/-! ### Degree-zero lifts across square-zero extensions -/

section Algebra

variable {R A B : Type u} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  {Λ : Type u} [AddCommGroup Λ]

/-- The degree-zero coefficient followed by `ψ` is multiplicative on elements whose
nonzero-degree coefficients land in a square-zero ideal. -/
theorem map_coeff_zero_mul {ψ : A →ₐ[R] B} {J : Ideal B} (hJ : J ^ 2 = ⊥)
    {x y : AddMonoidAlgebra A Λ} (hx : ∀ γ, γ ≠ 0 → ψ (x.coeff γ) ∈ J)
    (hy : ∀ γ, γ ≠ 0 → ψ (y.coeff γ) ∈ J) :
    ψ ((x * y).coeff 0) = ψ (x.coeff 0) * ψ (y.coeff 0) := by
  classical
  have hJJ : ∀ r s, r ∈ J → s ∈ J → r * s = 0 := by
    intro r s hr hs
    have h : r * s ∈ J ^ 2 := by rw [sq]; exact Ideal.mul_mem_mul hr hs
    rw [hJ] at h
    exact (Submodule.mem_bot _).mp h
  rw [coeff_mul, Finsupp.sum, map_sum, Finset.sum_eq_single 0]
  · rw [Finsupp.sum, map_sum, Finset.sum_eq_single 0]
    · simp
    · intro n _ hn
      simp [hn]
    · intro h0
      simp [Finsupp.notMem_support_iff.mp h0]
  · intro m _ hm
    rw [Finsupp.sum, map_sum]
    apply Finset.sum_eq_zero
    intro n _
    split_ifs with hmn
    · rw [map_mul]
      refine hJJ _ _ (hx m hm) (hy n ?_)
      rintro rfl
      exact hm (by simpa using hmn)
    · exact map_zero ψ
  · intro h0
    simp [Finsupp.notMem_support_iff.mp h0]

variable (ρ : A →ₐ[R] AddMonoidAlgebra A Λ)

/-- The degree-zero modification `a ↦ ψ ((ρ a)₀)` of an algebra map whose
nonzero-degree values lie in a square-zero ideal. -/
def degreeZeroLift (ψ : A →ₐ[R] B) {J : Ideal B} (hJ : J ^ 2 = ⊥)
    (hψ : ∀ a γ, γ ≠ 0 → ψ ((ρ a).coeff γ) ∈ J) : A →ₐ[R] B where
  toFun a := ψ ((ρ a).coeff 0)
  map_one' := by simp [AddMonoidAlgebra.one_def]
  map_mul' a b := by rw [map_mul]; exact map_coeff_zero_mul hJ (hψ a) (hψ b)
  map_zero' := by simp
  map_add' a b := by simp
  commutes' r := by
    rw [AlgHom.commutes, coe_algebraMap]
    simp

theorem degreeZeroLift_apply (ψ : A →ₐ[R] B) {J : Ideal B} (hJ : J ^ 2 = ⊥)
    (hψ : ∀ a γ, γ ≠ 0 → ψ ((ρ a).coeff γ) ∈ J) (a : A) :
    degreeZeroLift ρ ψ hJ hψ a = ψ ((ρ a).coeff 0) := rfl

/-- With the counit law, a map killing all nonzero-degree coefficients only sees the
degree-zero coefficient. -/
theorem map_eq_map_coeff_zero (hε : ∀ a, (ρ a).coeff.sum (fun _ r => r) = a)
    {B' : Type u} [CommRing B'] [Algebra R B'] (f : A →ₐ[R] B')
    (hf : ∀ a γ, γ ≠ 0 → f ((ρ a).coeff γ) = 0) (a : A) :
    f a = f ((ρ a).coeff 0) := by
  conv_lhs => rw [← hε a]
  rw [map_finsuppSum, Finsupp.sum_eq_single 0]
  · intro γ _ hγ
    exact hf a γ hγ
  · intro _
    exact map_zero f

end Algebra

/-! ### Monomial evaluations -/

section Monomial

variable {R A B : Type u} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  {Λ : Type u} [AddCommGroup Λ]

omit [AddCommGroup Λ] in
theorem liftNC_apply [AddMonoid Λ] (f : A →+ B) (g : Multiplicative Λ → B) (x : AddMonoidAlgebra A Λ) :
    liftNC f g x = x.coeff.sum fun γ r => f r * g (.ofAdd γ) := by
  conv_lhs => rw [← sum_coeff_single x]
  rw [map_finsuppSum]
  simp only [liftNC_single]

/-- Evaluating the monomials at themselves after a base map is the induced map of
group algebras. -/
theorem liftNCAlgHom_singleZero (f : A →ₐ[R] B) :
    liftNCAlgHom ((singleZeroAlgHom (R := R) (M := Λ)).comp f)
        ((Units.coeHom (AddMonoidAlgebra B Λ)).comp (of B Λ).toHomUnits)
        (fun _ _ => Commute.all _ _) = mapAlgHom Λ f := by
  apply algHom_ext
  · intro m
    simp
  · apply AlgHom.ext
    intro r
    simp

/-- On an element whose nonzero-degree coefficients die under `f`, evaluation at any
character only sees the degree-zero coefficient. -/
theorem liftNCAlgHom_apply_of_coeff (f : A →ₐ[R] B) (χ : Multiplicative Λ →* Bˣ)
    (x : AddMonoidAlgebra A Λ) (hx : ∀ γ, γ ≠ 0 → f (x.coeff γ) = 0) :
    liftNCAlgHom f ((Units.coeHom B).comp χ) (fun _ _ => Commute.all _ _) x = f (x.coeff 0) := by
  rw [coe_liftNCAlgHom, liftNC_apply, Finsupp.sum_eq_single 0]
  · simp
  · intro γ _ hγ
    simp [hx γ hγ]
  · intro _
    simp

/-- Evaluating monomials at inner monomials placed in outer degree zero is the outer
degree-zero inclusion. -/
theorem liftNCAlgHom_singleZero_singleZero :
    liftNCAlgHom ((singleZeroAlgHom : AddMonoidAlgebra A Λ →ₐ[R]
        AddMonoidAlgebra (AddMonoidAlgebra A Λ) Λ).comp
          (singleZeroAlgHom : A →ₐ[R] AddMonoidAlgebra A Λ))
      ((Units.coeHom (AddMonoidAlgebra (AddMonoidAlgebra A Λ) Λ)).comp
        ((Units.map (singleZeroAlgHom : AddMonoidAlgebra A Λ →ₐ[R]
          AddMonoidAlgebra (AddMonoidAlgebra A Λ) Λ).toMonoidHom).comp (of A Λ).toHomUnits))
      (fun _ _ => Commute.all _ _) = singleZeroAlgHom := by
  apply algHom_ext
  · intro m
    simp
  · apply AlgHom.ext
    intro r
    simp

/-- Evaluating monomials at a character sending `γ` to the doubly homogeneous monomial
`X^γ Y^γ` puts each homogeneous component in the matching outer degree. -/
theorem coeff_liftNCAlgHom_diag
    (χ : Multiplicative Λ →* (AddMonoidAlgebra (AddMonoidAlgebra A Λ) Λ)ˣ)
    (hχ : ∀ γ, (χ (.ofAdd γ) : AddMonoidAlgebra (AddMonoidAlgebra A Λ) Λ) = single γ (single γ 1))
    (y : AddMonoidAlgebra A Λ) (n : Λ) :
    (liftNCAlgHom ((singleZeroAlgHom : AddMonoidAlgebra A Λ →ₐ[R]
        AddMonoidAlgebra (AddMonoidAlgebra A Λ) Λ).comp
          (singleZeroAlgHom : A →ₐ[R] AddMonoidAlgebra A Λ))
      ((Units.coeHom (AddMonoidAlgebra (AddMonoidAlgebra A Λ) Λ)).comp χ)
      (fun _ _ => Commute.all _ _) y).coeff n = single n (y.coeff n) := by
  classical
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, coeff_add, Finsupp.add_apply, hx, hy, coeff_add,
      Finsupp.add_apply, single_add]
  | single γ r =>
    simp only [coe_liftNCAlgHom, liftNC_single, MonoidHom.coe_comp, Function.comp_apply,
      Units.coeHom_apply, hχ]
    by_cases h : γ = n
    · subst h
      simp [single_mul_single]
    · simp [single_mul_single, Finsupp.single_eq_of_ne' h]

end Monomial

/-! ### The coaction of a diagonalizable action on coordinates -/

section Geometry

variable {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]
  {G : GroupScheme (Spec R)} [IsAffineHom G.X.hom]
  (a : AutomorphicAction (groupScheme R Λ).toGrp G)

/-- Points of `D(Λ)` over `Spec B` are characters `Λ → Bˣ`. -/
def charEquiv (B : Type u) [CommRing B] [Algebra R B] :
    ((algSpec R).obj (op (CommAlgCat.of R B)) ⟶ (groupScheme R Λ).toGrp.X) ≃*
      (Multiplicative Λ →* Bˣ) :=
  Corepresented.affinePointsEquiv (functor R Λ) (grpCorepresentation R Λ) (CommAlgCat.of R B)

theorem charEquiv_map (B : Type u) [CommRing B] [Algebra R B]
    (f : algebra R Λ ⟶ CommAlgCat.of R B) :
    charEquiv B ((algSpec R).map f.op) = (grpCorepresentation R Λ).homEquiv f :=
  Corepresented.affinePointsEquiv_map _ _ _ f

theorem charEquiv_naturality {B B' : Type u} [CommRing B] [Algebra R B] [CommRing B']
    [Algebra R B'] (e : B →ₐ[R] B')
    (x : (algSpec R).obj (op (CommAlgCat.of R B)) ⟶ (groupScheme R Λ).toGrp.X) :
    charEquiv B' ((algSpec R).map (CommAlgCat.ofHom e).op ≫ x) =
      (Units.map e.toMonoidHom).comp (charEquiv B x) :=
  Corepresented.affinePointsEquiv_naturality _ _ (CommAlgCat.ofHom e) x

/-- The point of `D(Λ)` over `Spec B` given by a character `χ : Λ → Bˣ`. -/
def charPt (B : Type u) [CommRing B] [Algebra R B] (χ : Multiplicative Λ →* Bˣ) :
    (algSpec R).obj (op (CommAlgCat.of R B)) ⟶ (groupScheme R Λ).toGrp.X :=
  (charEquiv B).symm χ

theorem charPt_eq (B : Type u) [CommRing B] [Algebra R B] (χ : Multiplicative Λ →* Bˣ) :
    charPt B χ = (algSpec R).map (lift R Λ (B := CommAlgCat.of R B) χ).op := by
  apply (charEquiv B).injective
  rw [charPt, MulEquiv.apply_symm_apply, charEquiv_map]
  exact (((grpCorepresentation R Λ).homEquiv (Y := CommAlgCat.of R B)).apply_symm_apply χ).symm

theorem charPt_mul (B : Type u) [CommRing B] [Algebra R B] (χ χ' : Multiplicative Λ →* Bˣ) :
    charPt (R := R) B (χ * χ') = charPt B χ * charPt B χ' :=
  map_mul (charEquiv (R := R) (Λ := Λ) B).symm χ χ'

theorem charPt_one (B : Type u) [CommRing B] [Algebra R B] :
    charPt (R := R) (Λ := Λ) B 1 = 1 :=
  map_one (charEquiv (R := R) (Λ := Λ) B).symm

/-- Restricting a character point along an algebra map composes the character with it. -/
theorem map_comp_charPt {B B' : Type u} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
    (e : B →ₐ[R] B') (χ : Multiplicative Λ →* Bˣ) :
    (algSpec R).map (CommAlgCat.ofHom e).op ≫ charPt B χ =
      charPt B' ((Units.map e.toMonoidHom).comp χ) := by
  apply (charEquiv B').injective
  rw [charEquiv_naturality, charPt, charPt, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

/-- The coaction `ρ : A → A[Λ]` on the chosen coordinate algebra `A` of `G`: the
coordinates of the action of the universal character on the base point. -/
def coaction :
    Lie.coordinateAlgebra G →ₐ[R] AddMonoidAlgebra (Lie.coordinateAlgebra G) Λ :=
  Lie.pointCoordinates G
    (a.act (charPt _ (of (Lie.coordinateAlgebra G) Λ).toHomUnits)
      ((Lie.pointCoordinates G).symm singleZeroAlgHom))

/-- The action of a character point on an affine point, in coordinates. -/
theorem pointCoordinates_act (B : Type u) [CommRing B] [Algebra R B]
    (χ : Multiplicative Λ →* Bˣ) (g : Lie.AffinePoints G B) :
    Lie.pointCoordinates G (a.act (charPt B χ) g) =
      (liftNCAlgHom (Lie.pointCoordinates G g) ((Units.coeHom B).comp χ)
        (fun _ _ => Commute.all _ _)).comp (coaction a) := by
  set e := liftNCAlgHom (Lie.pointCoordinates G g) ((Units.coeHom B).comp χ)
    (fun _ _ => Commute.all _ _)
  have h1 : Lie.affineMap G e ((Lie.pointCoordinates G).symm singleZeroAlgHom) = g := by
    apply (Lie.pointCoordinates G).injective
    rw [Lie.pointCoordinates_naturality, Equiv.apply_symm_apply]
    apply AlgHom.ext
    intro r
    simp [e]
  have h2 : (Units.map e.toMonoidHom).comp
      (of (Lie.coordinateAlgebra G) Λ).toHomUnits = χ := by
    apply MonoidHom.ext
    intro m
    apply Units.ext
    simp [e]
  have h3 : (algSpec R).map (CommAlgCat.ofHom e).op ≫
      a.act (charPt _ (of (Lie.coordinateAlgebra G) Λ).toHomUnits)
        ((Lie.pointCoordinates G).symm singleZeroAlgHom) = a.act (charPt B χ) g := by
    rw [a.naturality, map_comp_charPt, h2, ← Lie.affineMap_apply, h1]
  rw [← h3, ← Lie.affineMap_apply, Lie.pointCoordinates_naturality]
  rfl

/-- The counit law: summing the coefficients of the coaction recovers the coordinate. -/
theorem coaction_counit (x : Lie.coordinateAlgebra G) :
    ((coaction a x).coeff.sum fun _ r => r) = x := by
  have h := pointCoordinates_act a (Lie.coordinateAlgebra G) 1
    ((Lie.pointCoordinates G).symm (AlgHom.id R _))
  rw [charPt_one, a.act_one_left, Equiv.apply_symm_apply] at h
  have hx := congrArg (fun φ => φ x) h
  simp only [AlgHom.id_apply, AlgHom.comp_apply, coe_liftNCAlgHom, liftNC_apply] at hx
  simpa using hx.symm

/-- Homogeneity: each coefficient of the coaction is homogeneous of its degree. -/
theorem coaction_coeff (x : Lie.coordinateAlgebra G) (n : Λ) :
    coaction a ((coaction a x).coeff n) = single n ((coaction a x).coeff n) := by
  have h := a.act_mul_left
    (charPt (AddMonoidAlgebra (AddMonoidAlgebra (Lie.coordinateAlgebra G) Λ) Λ)
      (of (AddMonoidAlgebra (Lie.coordinateAlgebra G) Λ) Λ).toHomUnits)
    (charPt (AddMonoidAlgebra (AddMonoidAlgebra (Lie.coordinateAlgebra G) Λ) Λ)
      ((Units.map (singleZeroAlgHom : AddMonoidAlgebra (Lie.coordinateAlgebra G) Λ →ₐ[R]
          AddMonoidAlgebra (AddMonoidAlgebra (Lie.coordinateAlgebra G) Λ) Λ).toMonoidHom).comp
        (of (Lie.coordinateAlgebra G) Λ).toHomUnits))
    ((Lie.pointCoordinates G).symm
      ((singleZeroAlgHom : AddMonoidAlgebra (Lie.coordinateAlgebra G) Λ →ₐ[R]
        AddMonoidAlgebra (AddMonoidAlgebra (Lie.coordinateAlgebra G) Λ) Λ).comp
          (singleZeroAlgHom : Lie.coordinateAlgebra G →ₐ[R]
            AddMonoidAlgebra (Lie.coordinateAlgebra G) Λ)))
  rw [← charPt_mul] at h
  have h' := congrArg (Lie.pointCoordinates G) h
  rw [pointCoordinates_act, pointCoordinates_act, pointCoordinates_act, Equiv.apply_symm_apply,
    liftNCAlgHom_singleZero_singleZero, liftNCAlgHom_singleZero] at h'
  have hx := congrArg (fun φ => (φ x).coeff n) h'
  simp only [AlgHom.comp_apply] at hx
  rw [coeff_liftNCAlgHom_diag _ (fun γ => by
    erw [MonoidHom.mul_apply, Units.val_mul]
    simp [single_mul_single]), coeff_mapAlgHom] at hx
  exact hx.symm

/-- An affine fixed point has coordinates killing the nonzero-degree coaction
coefficients. -/
theorem pointCoordinates_coeff_eq_zero {B : Type u} [CommRing B] [Algebra R B]
    {g : Lie.AffinePoints G B} (hg : a.IsFixed g) (x : Lie.coordinateAlgebra G) {γ : Λ}
    (hγ : γ ≠ 0) : Lie.pointCoordinates G g ((coaction a x).coeff γ) = 0 := by
  classical
  have h := hg _ ((algSpec R).map
    (CommAlgCat.ofHom (singleZeroAlgHom : B →ₐ[R] AddMonoidAlgebra B Λ)).op)
    (charPt _ (of B Λ).toHomUnits)
  rw [← Lie.affineMap_apply] at h
  have h' := congrArg (Lie.pointCoordinates G) h
  rw [pointCoordinates_act, Lie.pointCoordinates_naturality, liftNCAlgHom_singleZero] at h'
  have hx := congrArg (fun φ => (φ x).coeff γ) h'
  simp only [AlgHom.comp_apply, coeff_mapAlgHom] at hx
  rw [hx]
  simp [Finsupp.single_eq_of_ne hγ]

/-- A point over `Spec B` whose coordinates kill the nonzero-degree coaction coefficients
is fixed, on every refinement. -/
theorem isFixed_of_coeff {B : Type u} [CommRing B] [Algebra R B] (g : Lie.AffinePoints G B)
    (hg : ∀ x γ, γ ≠ 0 → Lie.pointCoordinates G g ((coaction a x).coeff γ) = 0) :
    a.IsFixed g := by
  intro T' b h
  let adj := algΓAlgSpecAdjunction R
  have key : ∀ {Y : (CommAlgCat.{u} R)ᵒᵖ} (f : T' ⟶ (algSpec R).obj Y),
      f = adj.unit.app T' ≫ (algSpec R).map ((adj.homEquiv T' Y).symm f) := fun f => by
    have hf := (adj.homEquiv T' _).apply_symm_apply f
    rw [Adjunction.homEquiv_unit] at hf
    exact hf.symm
  let B' : CommAlgCat.{u} R := ((algΓ R).obj T').unop
  let c : T' ⟶ (algSpec R).obj (op (CommAlgCat.of R B')) := adj.unit.app T'
  let e : B →ₐ[R] B' := ((adj.homEquiv T' _).symm b).unop.hom
  let χ : Multiplicative Λ →* B'ˣ := charEquiv B'
    ((algSpec R).map ((adj.homEquiv T' (op (algebra R Λ))).symm h))
  have hb : b = c ≫ (algSpec R).map (CommAlgCat.ofHom e).op := key b
  have hh : h = c ≫ charPt B' χ := by
    have e1 : charPt B' χ = (algSpec R).map ((adj.homEquiv T' (op (algebra R Λ))).symm h) :=
      (charEquiv (R := R) (Λ := Λ) B').symm_apply_apply _
    exact (key (Y := op (algebra R Λ)) h).trans (congrArg (fun t => c ≫ t) e1.symm)
  have hfix : a.act (charPt B' χ) (Lie.affineMap G e g) = Lie.affineMap G e g := by
    apply (Lie.pointCoordinates G).injective
    rw [pointCoordinates_act, Lie.pointCoordinates_naturality]
    apply AlgHom.ext
    intro x
    rw [AlgHom.comp_apply, liftNCAlgHom_apply_of_coeff, AlgHom.comp_apply, AlgHom.comp_apply,
      ← map_eq_map_coeff_zero (coaction a) (coaction_counit a) (Lie.pointCoordinates G g) hg x]
    intro γ hγ
    rw [AlgHom.comp_apply, hg x γ hγ, map_zero]
  rw [hh, hb, Category.assoc, ← a.naturality, ← Lie.affineMap_apply, hfix]

/-- The coordinate algebra of a representative of the fixed subgroup is formally smooth
when that of `G` is. -/
theorem formallySmooth_of_isRepresentedBy {C : GroupScheme (Spec R)} [IsAffineHom C.X.hom]
    (j : C ⟶ G) (hrep : a.fixedSubgroup.IsRepresentedBy j)
    [Algebra.FormallySmooth R (Lie.coordinateAlgebra G)] :
    Algebra.FormallySmooth R (Lie.coordinateAlgebra C) := by
  have := hrep.1
  refine Algebra.FormallySmooth.of_comp_surjective fun B _ _ I hI f => ?_
  let x0 : Lie.AffinePoints C (B ⧸ I) := (Lie.pointCoordinates C).symm f
  have hy0 : a.IsFixed (x0 ≫ j.hom.hom) := by
    have hmem : x0 ≫ j.hom.hom ∈ (SubgroupFunctor.range j).carrier _ := ⟨x0, rfl⟩
    rw [hrep.2] at hmem
    exact hmem
  let g0 := Lie.pointCoordinates G (x0 ≫ j.hom.hom)
  have hg0 : ∀ x γ, γ ≠ 0 → g0 ((coaction a x).coeff γ) = 0 := fun x _ hγ =>
    pointCoordinates_coeff_eq_zero a hy0 x hγ
  obtain ⟨ψ, hψ⟩ := Algebra.FormallySmooth.comp_surjective R (Lie.coordinateAlgebra G) I hI g0
  have hψI : ∀ x γ, γ ≠ 0 → ψ ((coaction a x).coeff γ) ∈ I := by
    intro x γ hγ
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk R, ← AlgHom.comp_apply, hψ]
    exact hg0 x γ hγ
  let ψ' := degreeZeroLift (coaction a) ψ hI hψI
  have hψ'0 : ∀ x γ, γ ≠ 0 → ψ' ((coaction a x).coeff γ) = 0 := by
    intro x γ hγ
    rw [degreeZeroLift_apply, coaction_coeff, coeff_single, Finsupp.single_eq_of_ne' hγ,
      map_zero]
  have hψ' : (Ideal.Quotient.mkₐ R I).comp ψ' = g0 := by
    apply AlgHom.ext
    intro x
    rw [AlgHom.comp_apply, degreeZeroLift_apply, ← AlgHom.comp_apply, hψ,
      ← map_eq_map_coeff_zero (coaction a) (coaction_counit a) g0 hg0 x]
  have hfix := isFixed_of_coeff a ((Lie.pointCoordinates G).symm ψ')
    (by simpa only [Equiv.apply_symm_apply] using hψ'0)
  obtain ⟨x, hx⟩ : ∃ x, x ≫ j.hom.hom = (Lie.pointCoordinates G).symm ψ' := by
    have hmem : (Lie.pointCoordinates G).symm ψ' ∈ a.fixedSubgroup.carrier _ := hfix
    rw [← hrep.2] at hmem
    exact hmem
  refine ⟨Lie.pointCoordinates C x, ?_⟩
  have hx0 : Lie.affineMap C (Ideal.Quotient.mkₐ R I) x = x0 := by
    rw [← cancel_mono j.hom.hom]
    apply (Lie.pointCoordinates G).injective
    rw [Lie.affineMap_apply, Category.assoc, hx, ← Lie.affineMap_apply,
      Lie.pointCoordinates_naturality, Equiv.apply_symm_apply, hψ']
  rw [← Lie.pointCoordinates_naturality, hx0, Equiv.apply_symm_apply]

end Geometry

/-- **CGP, Proposition A.8.10(2).** A closed representative of the fixed subgroup of a
diagonalizable action on a smooth affine group over a field is smooth. -/
theorem fixedSubgroupSmooth : FixedSubgroupSmoothStatement.{u} := by
  intro k _ Λ _ _ G hG hGa a C j hrep hcl
  have := hG
  have := hGa
  have : IsClosedImmersion j.hom.hom.left := hcl
  have : IsAffineHom C.X.hom := by
    have h' : IsAffineHom (j.hom.hom.left ≫ G.X.hom) := inferInstance
    simpa only [Over.w] using h'
  have := FixedSubgroupSmoothAlgebraBridge.coordinateAlgebra_smooth G
  exact FixedSubgroupSmoothAlgebraBridge.smooth_of_formallySmooth j
    (formallySmooth_of_isRepresentedBy a j hrep)

end Langlands.GroupScheme.Diagonalizable.FixedSmooth
