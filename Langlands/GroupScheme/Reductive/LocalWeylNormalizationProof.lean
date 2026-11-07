import Langlands.GroupScheme.Reductive.LocalWeylNormalizationStatement
import Langlands.GroupScheme.Reductive.LocalRootGroupParam
import Langlands.GroupScheme.Reductive.LocalSplitFieldPoints
import Langlands.GroupScheme.Reductive.LocalSplitFieldComparison
import Langlands.GroupScheme.Reductive.LocalSplitWeylFamily
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-! # Weyl normalization over a reduced local ring from the field case -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalWeylNormalization

open LocalSplitCell LocalSplitBigCell

/-! ### Big-cell points with one nonzero root coordinate on each side -/

section Cell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))}

omit [Fintype I] in
theorem list_prod_ofFn_eq {M : Type*} [Monoid M] {r : ℕ} (f : Fin r → M) (k₀ : Fin r)
    (hf : ∀ k, k ≠ k₀ → f k = 1) : (List.ofFn f).prod = f k₀ := by
  induction r with
  | zero => exact k₀.elim0
  | succ r ih =>
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases ?_ (fun j hj => ?_) k₀ hf
    · intro h0
      rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      exact h0 j.succ (Fin.succ_ne_zero j)
    · rw [hj 0 (Fin.succ_ne_zero j).symm, one_mul]
      exact ih (fun k => f k.succ) j (fun k hk => hj k.succ (fun h => hk (Fin.succ_injective _ h)))

omit [Fintype I] in
/-- An ordered product with a single nonzero coordinate is that root value. -/
theorem orderedProduct_single (u : J → (Ga R ⟶ G)) {r : ℕ} (e : Fin r → J)
    (Z : Over (Spec (CommRingCat.of R))) (k₀ : Fin r) (c : Γ(Z.left, ⊤)) :
    orderedProduct u e Z (Pi.single k₀ c) = rootPoint (u (e k₀)) Z c := by
  rw [orderedProduct, list_prod_ofFn_eq _ k₀, Pi.single_eq_same]
  intro k hk
  rw [Pi.single_eq_of_ne hk, rootPoint_zero]

/-- The cell formula with one nonzero negative and one nonzero positive coordinate. -/
theorem cellPoint_single (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (u : J → (Ga R ⟶ G))
    {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J) (Z : Over (Spec (CommRingCat.of R)))
    (kn : Fin m) (y : Γ(Z.left, ⊤)) (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X)
    (kp : Fin n) (x : Γ(Z.left, ⊤)) :
    cellPoint i u neg pos Z (Pi.single kn y) t (Pi.single kp x) =
      rootPoint (u (neg kn)) Z y * (t ≫ i.hom.hom) * rootPoint (u (pos kp)) Z x := by
  rw [cellPoint, orderedProduct_single, orderedProduct_single]

/-- If the big-cell map is a monomorphism, the positive coordinates of a cell point are
determined by the point. -/
theorem posCoord_eq_of_cellPoint_eq (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (u : J → (Ga R ⟶ G)) {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J)
    [Mono (cellMap i u neg pos).left] {Z : Over (Spec (CommRingCat.of R))}
    {v v' : Fin m → Γ(Z.left, ⊤)} {t t' : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X}
    {w w' : Fin n → Γ(Z.left, ⊤)}
    (h : cellPoint i u neg pos Z v t w = cellPoint i u neg pos Z v' t' w') : w = w' := by
  obtain ⟨x, hx⟩ := (coordTriple_bijective R I m n Z).2 (v, t, w)
  obtain ⟨x', hx'⟩ := (coordTriple_bijective R I m n Z).2 (v', t', w')
  simp only [coordTriple, Prod.mk.injEq] at hx hx'
  have hxx : x ≫ cellMap i u neg pos = x' ≫ cellMap i u neg pos := by
    rw [comp_cellMap, comp_cellMap, hx.1, hx.2.1, hx.2.2, hx'.1, hx'.2.1, hx'.2.2, h]
  have : x = x' := by
    apply Over.OverMorphism.ext
    rw [← cancel_mono (cellMap i u neg pos).left, ← Over.comp_left, ← Over.comp_left, hxx]
  rw [← hx.2.2, ← hx'.2.2, this]

end Cell

/-! ### Weyl points from field points -/

section WeylFields

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))}

/-- Over a field-valued base change, the Weyl-point identity of the base-changed root maps is
the Weyl-point identity of the original root maps on the test schemes coming from the field. -/
theorem isWeylPoint_apply_of_baseChange {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {u v : Ga R ⟶ G} {f : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)} (K : Type u) [Field K] [Algebra R K]
    (h : IsWeylPoint (splitTorus.baseChangeHom (K := K) G I i)
      (weylPoint (baseChangeRoot K u) (baseChangeRoot K v)) f)
    (Z : Over (Spec (CommRingCat.of K)))
    (t : (Over.map (algebraBaseMap R K)).obj Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) :
    (toUnit _ ≫ weylPoint u v) * (t ≫ i.hom.hom) * (toUnit _ ≫ weylPoint u v)⁻¹ =
      t ≫ (splitTorus.exponentIso _ I f).hom.hom.hom ≫ i.hom.hom := by
  let E := GroupScheme.baseChangePointsEquiv (algebraBaseMap R K) G Z
  let ET := GroupScheme.baseChangePointsEquiv (algebraBaseMap R K) (splitTorus _ I) Z
  let Z' := (Over.map (algebraBaseMap R K)).obj Z
  obtain ⟨t₀, rfl⟩ : ∃ t₀ : Z ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X,
      ET (t₀ ≫ (splitTorus.baseChangeIso (algebraBaseMap R K) I).inv.hom.hom) = t := by
    refine ⟨ET.symm t ≫ (splitTorus.baseChangeIso (algebraBaseMap R K) I).hom.hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id,
      MulEquiv.apply_symm_apply]
  have hN : E (toUnit Z ≫ weylPoint (baseChangeRoot K u) (baseChangeRoot K v)) =
      toUnit Z' ≫ weylPoint u v := by
    rw [toUnit_comp_eq_constantPoint, constantPoint_weylPoint, map_mul, map_mul,
      baseChangePointsEquiv_rootPoint, baseChangePointsEquiv_rootPoint,
      toUnit_comp_eq_constantPoint, constantPoint_weylPoint]
  have hexp : (splitTorus.exponentIso (Spec (CommRingCat.of K)) I f).hom ≫
      (splitTorus.baseChangeIso (algebraBaseMap R K) I).inv =
        (splitTorus.baseChangeIso (algebraBaseMap R K) I).inv ≫
          (GroupScheme.baseChange (algebraBaseMap R K)).map
            (splitTorus.exponentIso (Spec (CommRingCat.of R)) I f).hom := by
    rw [Iso.eq_inv_comp, ← Category.assoc,
      splitTorus.exponentIso_baseChange (Spec (CommRingCat.of R)) I (algebraBaseMap R K) f,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have ht : ET ((t₀ ≫ (splitTorus.exponentIso _ I f).hom.hom.hom) ≫
      (splitTorus.baseChangeIso (algebraBaseMap R K) I).inv.hom.hom) =
        ET (t₀ ≫ (splitTorus.baseChangeIso (algebraBaseMap R K) I).inv.hom.hom) ≫
          (splitTorus.exponentIso (Spec (CommRingCat.of R)) I f).hom.hom.hom := by
    rw [← GroupScheme.baseChangePointsEquiv_comp, Category.assoc, Category.assoc,
      ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, hexp]
  have hw := congrArg E (h Z t₀)
  rw [map_mul, map_mul, map_inv, hN, baseChangePointsEquiv_torus, ← Category.assoc,
    baseChangePointsEquiv_torus, ht, Category.assoc] at hw
  exact hw

/-- **Weyl points from field points.** Over a reduced ring, the Weyl point of two root maps
normalizes the torus through `f` as soon as this holds after base change to every field. -/
theorem isWeylPoint_of_baseChange [IsReduced R] [IsAffineHom G.X.hom]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {u v : Ga R ⟶ G}
    {f : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)}
    (h : ∀ (K : Type u) [Field K] [Algebra R K],
      IsWeylPoint (splitTorus.baseChangeHom (K := K) G I i)
        (weylPoint (baseChangeRoot K u) (baseChangeRoot K v)) f) :
    IsWeylPoint i (weylPoint u v) f := by
  have : IsReduced (splitTorus (Spec (CommRingCat.of R)) I).X.left := by
    have := smooth_splitTorus (S := Spec (CommRingCat.of R)) I
    exact Langlands.AlgebraicGeometry.SmoothReducedBase.isReduced_of_smooth_of_isReduced
      (splitTorus (Spec (CommRingCat.of R)) I).X.hom
  have key : (toUnit _ ≫ weylPoint u v) * i.hom.hom * (toUnit _ ≫ weylPoint u v)⁻¹ =
      (splitTorus.exponentIso _ I f).hom.hom.hom ≫ i.hom.hom := by
    apply LocalRootGroup.ext_of_fieldPoints
    intro K _ s w
    obtain ⟨_, rfl⟩ := LocalRootGroup.exists_algebra_of_fieldPoint (R := R) s
    let e : Over.mk (algebraBaseMap R K) ≅ fieldPoint R K := Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ 𝟙 _ ≫ algebraBaseMap R K = algebraBaseMap R K
      rw [Category.id_comp, Category.id_comp])
    have h1 := congrArg (fun z => e.hom ≫ z)
      (isWeylPoint_apply_of_baseChange K (h K) (𝟙_ _) (e.inv ≫ w))
    simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, comp_toUnit, Iso.hom_inv_id,
      Category.id_comp] at h1
    simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, comp_toUnit]
    exact h1
  intro Z t
  have h2 := congrArg (fun z => t ≫ z) key
  simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, comp_toUnit] at h2
  simpa only [Category.assoc] using h2

end WeylFields

/-! ### Global functions on spectra -/

section Gamma

theorem specMap_appTop_inv {A B : CommRingCat.{u}} (f : A ⟶ B) (a : A) :
    (Spec.map f).appTop ((Scheme.ΓSpecIso A).inv a) = (Scheme.ΓSpecIso B).inv (f a) := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]

theorem ΓSpecIso_hom_specMap_appTop {A B : CommRingCat.{u}} (f : A ⟶ B)
    (x : Γ(Spec A, ⊤)) :
    (Scheme.ΓSpecIso B).hom ((Spec.map f).appTop x) = f ((Scheme.ΓSpecIso A).hom x) := by
  rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]

end Gamma

/-! ### Lifting points along open immersions -/

/-- A point of `Y` lifts along an open immersion `X ⟶ Y` if it does so after precomposition
with a surjective morphism. -/
theorem exists_lift_of_surjective {S : Scheme.{u}} {X Y Z W : Over S} (j : X ⟶ Y)
    [IsOpenImmersion j.left] (g : Z ⟶ Y) (s : W ⟶ Z) (hs : Function.Surjective s.left)
    (x₀ : W ⟶ X) (h : s ≫ g = x₀ ≫ j) : ∃ y : Z ⟶ X, y ≫ j = g := by
  have H : Set.range g.left ⊆ Set.range j.left := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, rfl⟩ := hs p
    refine ⟨x₀.left q, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ← h, Over.comp_left, Scheme.Hom.comp_apply]
  refine ⟨Over.homMk (IsOpenImmersion.lift j.left g.left H) ?_, ?_⟩
  · rw [← Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w g]
  · apply Over.OverMorphism.ext
    rw [Over.comp_left]
    exact IsOpenImmersion.lift_fac _ _ _

/-! ### Dual numbers -/

section Dual

open Corepresented.RingCoordinates

variable (R : Type u) [CommRing R]

/-- The spectrum of the dual numbers `R[ε]` over `Spec R`. -/
abbrev dualOver : Over (Spec (CommRingCat.of R)) :=
  specOver (CommRingCat.of R) (DualNumber R)

/-- The global function `ε` on `Spec R[ε]`. -/
def epsSec : Γ((dualOver R).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv DualNumber.eps

/-- The closed point inclusion `Spec R ⟶ Spec R[ε]`, given by `ε ↦ 0`. -/
abbrev dualZero : specOver (CommRingCat.of R) R ⟶ dualOver R :=
  specMapOver (TrivSqZeroExt.fstHom R R R)

theorem surjective_dualZero : Function.Surjective (dualZero R).left := by
  have h := PrimeSpectrum.isHomeomorph_comap (TrivSqZeroExt.fstHom R R R).toRingHom
    (fun x => ⟨1, one_pos, TrivSqZeroExt.inl x, by simp⟩) (by
      intro x hx
      have hx' : x.fst = 0 := hx
      have hx2 : x = TrivSqZeroExt.inr x.snd := TrivSqZeroExt.ext hx' rfl
      refine ⟨2, ?_⟩
      rw [pow_two, hx2, TrivSqZeroExt.inr_mul_inr]
      exact Submodule.zero_mem _)
  exact h.surjective

theorem dualZero_appTop_epsSec : (dualZero R).left.appTop (epsSec R) = 0 := by
  change (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom)).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv DualNumber.eps) = 0
  rw [specMap_appTop_inv]
  change (Scheme.ΓSpecIso (CommRingCat.of R)).inv (DualNumber.eps : DualNumber R).fst = 0
  rw [DualNumber.fst_eps, map_zero]

variable {R} {I : Type u} [Fintype I] {J : Type u} {G : GroupScheme (Spec (CommRingCat.of R))}

/-- **The point `u(1) v(ε)` lies in the big cell.** Its reduction modulo `ε` is `u(1)`, a
point of the cell, and the cell is open. -/
theorem exists_dualCellLift (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (fam : J → (Ga R ⟶ G)) {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J)
    [IsOpenImmersion (cellMap i fam neg pos).left] (kn : Fin m) (kp : Fin n) :
    ∃ y : dualOver R ⟶ cellObj R I m n, y ≫ cellMap i fam neg pos =
      rootPoint (fam (pos kp)) _ 1 * rootPoint (fam (neg kn)) _ (epsSec R) := by
  let W := specOver (CommRingCat.of R) R
  obtain ⟨x₀, hx₀⟩ := (coordTriple_bijective R I m n W).2
    (Pi.single kn 0, 1, Pi.single kp 1)
  simp only [coordTriple, Prod.mk.injEq] at hx₀
  refine exists_lift_of_surjective _ _ (dualZero R) (surjective_dualZero R) x₀ ?_
  rw [comp_cellMap, hx₀.1, hx₀.2.1, hx₀.2.2, cellPoint_single, MonObj.comp_mul, comp_rootPoint,
    comp_rootPoint, dualZero_appTop_epsSec, map_one]
  simp only [rootPoint_zero, MonObj.one_comp, one_mul, mul_one]

end Dual

/-! ### The field computation -/

section FieldCoord

open Corepresented.RingCoordinates

variable {R : Type u} [CommRing R] (k : Type u) [Field k] [Algebra R k]

/-- The map `R[ε] → k[ε]`, `r + sε ↦ r + sε`. -/
def dualMap : DualNumber R →ₐ[R] DualNumber k :=
  DualNumber.lift ⟨(Algebra.ofId R (DualNumber k), DualNumber.eps), DualNumber.eps_mul_eps,
    fun _ => DualNumber.commute_eps_left _⟩

theorem dualMap_eps : dualMap k (DualNumber.eps : DualNumber R) = DualNumber.eps :=
  DualNumber.lift_apply_eps _

theorem snd_dualMap (x : DualNumber R) : (dualMap k x).snd = algebraMap R k x.snd := by
  rw [dualMap, DualNumber.lift_apply_apply]
  simp [Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl']

/-- The unit `1 + cε` of `k[ε]`. -/
def dualUnit (c : k) : (DualNumber k)ˣ where
  val := 1 + TrivSqZeroExt.inr c
  inv := 1 - TrivSqZeroExt.inr c
  val_inv := by
    rw [add_mul, one_mul, mul_sub, mul_one, TrivSqZeroExt.inr_mul_inr]
    abel
  inv_val := by
    rw [sub_mul, one_mul, mul_add, mul_one, TrivSqZeroExt.inr_mul_inr]
    abel

variable {k} {I : Type u} [Fintype I] {G : GroupScheme (Spec (CommRingCat.of R))}
  (D : Type u) [CommRing D] [Algebra R D] [Algebra k D] [IsScalarTower R k D]

theorem testOverHom_appTop (c : Γ((testOver k D).left, ⊤)) :
    (testOverHom (CommRingCat.of R) k D).left.appTop c = c := by
  change (𝟙 (Spec (CommRingCat.of D)) : _ ⟶ _).appTop c = c
  rw [Scheme.Hom.id_appTop]
  rfl

/-- Values of a base-changed root map over `Spec D`, regarded over `Spec R`. -/
theorem testOverHom_rootPoint (w : Ga R ⟶ G) (c : Γ((testOver k D).left, ⊤)) :
    testOverHom (CommRingCat.of R) k D ≫
        GroupScheme.baseChangePointsEquiv (algebraBaseMap R k) G (testOver k D)
          (rootPoint (baseChangeRoot k w) (testOver k D) c) =
      rootPoint w (specOver (CommRingCat.of R) D) c := by
  rw [baseChangePointsEquiv_rootPoint, comp_rootPoint, testOverHom_appTop]

/-- Torus values of the base-changed torus over `Spec D`, regarded over `Spec R`. -/
theorem testOverHom_torus (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (t : testOver k D ⟶ (splitTorus (Spec (CommRingCat.of k)) I).X) :
    testOverHom (CommRingCat.of R) k D ≫
        GroupScheme.baseChangePointsEquiv (algebraBaseMap R k) G (testOver k D)
          (t ≫ (splitTorus.baseChangeHom (K := k) G I i).hom.hom) =
      (testOverHom (CommRingCat.of R) k D ≫
        GroupScheme.baseChangePointsEquiv (algebraBaseMap R k) (splitTorus _ I) (testOver k D)
          (t ≫ (splitTorus.baseChangeIso (algebraBaseMap R k) I).inv.hom.hom)) ≫ i.hom.hom := by
  rw [baseChangePointsEquiv_torus, Category.assoc]

theorem baseScalar_testOver (d : k) :
    baseScalar (testOver k D) d = (Scheme.ΓSpecIso (CommRingCat.of D)).inv (algebraMap k D d) := by
  change (Spec.map (CommRingCat.ofHom (algebraMap k D))).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv d) = _
  rw [specMap_appTop_inv]
  rfl

theorem dualMap_appTop_epsSec :
    (specMapOver (dualMap (R := R) k)).left.appTop (epsSec R) =
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv DualNumber.eps := by
  change (Spec.map (CommRingCat.ofHom (dualMap (R := R) k).toRingHom)).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv DualNumber.eps) = _
  rw [specMap_appTop_inv]
  exact congrArg _ (dualMap_eps k)

variable {J : Type u}

/-- **The `ε`-coefficient on field fibres.** If `u(1) v(ε) = y ≫ cellMap` over `R[ε]` and,
over a field `k`, `u` and the rescaling `v(d ·)` satisfy the rank-one relation, then the
`ε`-coefficient of the `u`-coordinate of `y` maps to `-d⁻¹` in `k`. -/
theorem algebraMap_snd_posCoord (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (fam : J → (Ga R ⟶ G)) {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J)
    [Mono (cellMap i fam neg pos).left] (kn : Fin m) (kp : Fin n)
    (y : dualOver R ⟶ cellObj R I m n)
    (hy : y ≫ cellMap i fam neg pos =
      rootPoint (fam (pos kp)) _ 1 * rootPoint (fam (neg kn)) _ (epsSec R))
    (d : k) (hd : d ≠ 0)
    (χv : cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I))
    (hrel : RootCell.RelationOver (T := splitTorus.commGroupScheme _ I)
      (splitTorus.baseChangeHom (K := k) G I i) χv (baseChangeRoot k (fam (pos kp)))
      (scaleHom d ≫ baseChangeRoot k (fam (neg kn))) (testOver k (DualNumber k))) :
    algebraMap R k ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom
      (posCoord y kp)).snd = -d⁻¹ := by
  let Zk := testOver k (DualNumber k)
  let gam := (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv
  let u0 := dualUnit k d⁻¹
  let Uz : Γ(Zk.left, ⊤)ˣ := Units.map gam.hom.toMonoidHom u0
  have hR := hrel (VectorGroup.scalarPoint _ Zk 1)
    (VectorGroup.scalarPoint _ Zk (gam (TrivSqZeroExt.inr d⁻¹)))
    (VectorGroup.scalarPoint _ Zk (gam ↑u0⁻¹))
    (VectorGroup.scalarPoint _ Zk (gam ↑u0⁻¹ * gam (TrivSqZeroExt.inr d⁻¹))) Uz
    (by
      rw [RootCell.crd, RootCell.crd, VectorGroup.coordinates_scalarPoint,
        VectorGroup.coordinates_scalarPoint, one_mul]
      change gam (1 + TrivSqZeroExt.inr d⁻¹) = _
      rw [map_add, map_one])
    (by
      rw [RootCell.crd, RootCell.crd, VectorGroup.coordinates_scalarPoint,
        VectorGroup.coordinates_scalarPoint, mul_one]
      rfl)
    (by
      rw [RootCell.crd, RootCell.crd, VectorGroup.coordinates_scalarPoint,
        VectorGroup.coordinates_scalarPoint]
      rfl)
  let tk := (Gm.pointsEquiv _ Zk).symm Uz ≫ (CommGroupScheme.groupHom χv).hom.hom
  have htk : (Gm.pointsEquiv _ Zk).symm Uz ≫ (CommGroupScheme.groupHom χv).hom.hom ≫
      (splitTorus.baseChangeHom (K := k) G I i).hom.hom =
        tk ≫ (splitTorus.baseChangeHom (K := k) G I i).hom.hom := (Category.assoc _ _ _).symm
  rw [RootCell.RelationAt, htk] at hR
  change rootPoint _ Zk 1 * rootPoint _ Zk _ = rootPoint _ Zk _ * _ * rootPoint _ Zk _ at hR
  rw [rootPoint_scaleHom, rootPoint_scaleHom] at hR
  have hT := congrArg (fun x => testOverHom (CommRingCat.of R) k (DualNumber k) ≫
    GroupScheme.baseChangePointsEquiv (algebraBaseMap R k) G Zk x) hR
  simp only [map_mul, MonObj.comp_mul] at hT
  rw [testOverHom_rootPoint, testOverHom_rootPoint, testOverHom_rootPoint, testOverHom_rootPoint,
    testOverHom_torus] at hT
  have heps : ∀ x : Γ(Zk.left, ⊤), x = gam (TrivSqZeroExt.inr d⁻¹) →
      baseScalar Zk d * x = gam DualNumber.eps := by
    rintro x rfl
    rw [baseScalar_testOver]
    refine ((map_mul gam.hom _ _).symm).trans (congrArg gam.hom ?_)
    rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.inl_mul_inr, smul_eq_mul,
      mul_inv_cancel₀ hd]
    rfl
  rw [heps _ rfl] at hT
  let ψ : specOver (CommRingCat.of R) (DualNumber k) ⟶ dualOver R :=
    specMapOver (dualMap (R := R) k)
  have hcell := (comp_cellMap i fam neg pos (ψ ≫ y)).symm
  rw [Category.assoc, hy, MonObj.comp_mul, comp_rootPoint, comp_rootPoint, map_one,
    dualMap_appTop_epsSec, hT, ← cellPoint_single] at hcell
  have hp := congrFun (posCoord_eq_of_cellPoint_eq i fam neg pos hcell) kp
  rw [posCoord_comp, Pi.single_eq_same] at hp
  have hp2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom hp
  change (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom
    ((Spec.map (CommRingCat.ofHom (dualMap (R := R) k).toRingHom)).appTop (posCoord y kp)) =
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv ↑u0⁻¹) at hp2
  rw [ΓSpecIso_hom_specMap_appTop, Iso.inv_hom_id_apply] at hp2
  have hs := congrArg TrivSqZeroExt.snd hp2
  change (dualMap k _).snd = _ at hs
  rw [snd_dualMap] at hs
  rw [hs]
  change (1 - TrivSqZeroExt.inr d⁻¹ : DualNumber k).snd = -d⁻¹
  simp

end FieldCoord

end Langlands.GroupScheme.LocalWeylNormalization

/-! ### Weyl normalization over a reduced local ring -/

namespace Langlands.GroupScheme

open LocalSplitCell LocalSplitBigCell LocalWeylNormalization

/-- **Weyl normalization over a reduced local ring, from the field case.** Given `u` for a
simple root `a`, choose root parametrizations of all other roots and write `u(1) v(ε)` in the
big cell over `R[ε]`. The `ε`-coefficient `-c` of its `u`-coordinate maps to `-d⁻¹` over every
field, where `d` is the rescaling of the field case, so `c` is a unit; `v(c⁻¹ ·)` is then the
normalized parametrization of `-a`, as one checks at field points. -/
theorem localWeylNormalization_of_field (hF : FieldWeylNormalizationStatement.{u}) :
    LocalWeylNormalizationStatement.{u} := by
  intro R _ _ _ G _ hG I _ _ i hcl hmax J P hP b a ha u hu
  classical
  have := hP.finite
  have hpos : b.IsPos a := RootPairing.Base.isPos_of_mem_support ha
  have hneg : ¬ b.IsPos (P.reflectionPerm a a) := by
    intro h
    let _ := P.indexNeg
    change 0 < b.height (-a) at h
    rw [RootPairing.Base.height_reflectionPerm_self] at h
    rw [RootPairing.Base.isPos_iff] at hpos
    omega
  have hne : P.reflectionPerm a a ≠ a := fun h => hneg (by rw [h]; exact hpos)
  choose w hw using fun α => LocalRootGroup.exists_rootParametrization hG i hmax hP α
  let v := w (P.reflectionPerm a a)
  have hv : IsRootParametrization i (P.root (P.reflectionPerm a a)) v := hw _
  obtain ⟨fam, hfa, hfa', hfam⟩ : ∃ fam : J → (Ga R ⟶ G), fam a = u ∧
      fam (P.reflectionPerm a a) = v ∧ ∀ α, IsRootParametrization i (P.root α) (fam α) := by
    refine ⟨Function.update w a u, Function.update_self _ _ _,
      Function.update_of_ne hne _ _, fun α => ?_⟩
    by_cases h : α = a
    · subst h
      rw [Function.update_self]
      exact hu
    · rw [Function.update_of_ne h]
      exact hw α
  let neg := (Finite.equivFin {α // ¬ b.IsPos α}).symm
  let pos := (Finite.equivFin {α // b.IsPos α}).symm
  have := localSplitBigCell R G hG I i hcl hmax J P hP b fam hfam _ _ neg pos
  let kn := neg.symm ⟨P.reflectionPerm a a, hneg⟩
  let kp := pos.symm ⟨a, hpos⟩
  have hkn : fam (neg kn : J) = v := by
    rw [Equiv.apply_symm_apply]
    exact hfa'
  have hkp : fam (pos kp : J) = u := by
    rw [Equiv.apply_symm_apply]
    exact hfa
  obtain ⟨y, hy⟩ := exists_dualCellLift i fam (fun k => (neg k : J)) (fun k => (pos k : J)) kn kp
  let c : R := -((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom (posCoord y kp)).snd
  have hc : ∀ (k : Type u) [Field k] [Algebra R k] (d : k), d ≠ 0 →
      (∀ Z : Over (Spec (CommRingCat.of k)),
        RootCell.RelationOver (T := splitTorus.commGroupScheme _ I)
          (splitTorus.baseChangeHom (K := k) G I i)
          (splitTorus.exponentCocharacter _ I (P.coroot a)) (baseChangeRoot k u)
          (scaleHom d ≫ baseChangeRoot k v) Z) → algebraMap R k c = d⁻¹ := by
    intro k _ _ d hd hrel
    have h := algebraMap_snd_posCoord i fam (fun k => (neg k : J)) (fun k => (pos k : J)) kn kp
      y hy d hd _ (by rw [hkp, hkn]; exact hrel _)
    rw [map_neg, h, neg_neg]
  obtain ⟨d₀, hd₀, hrel₀, -⟩ := hF R G hG I i hmax J P hP a u v hu hv
    (IsLocalRing.ResidueField R)
  have hcu : IsUnit c := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← IsLocalRing.ResidueField.algebraMap_eq,
      hc _ d₀ hd₀ hrel₀]
    exact inv_ne_zero hd₀
  refine ⟨scaleHom (↑hcu.unit⁻¹ : R) ≫ v, hv.scale hcu.unit⁻¹, ?_⟩
  apply LocalWeylNormalization.isWeylPoint_of_baseChange
  intro K _ _
  obtain ⟨d, hd, hrel, hW⟩ := hF R G hG I i hmax J P hP a u v hu hv K
  have hd' : algebraMap R K (↑hcu.unit⁻¹ : R) = d := by
    rw [map_units_inv, IsUnit.unit_spec, hc K d hd hrel, inv_inv]
  rw [baseChangeRoot_scaleHom, hd']
  exact hW

end Langlands.GroupScheme
