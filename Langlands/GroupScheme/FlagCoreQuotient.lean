import Langlands.GroupScheme.Absolute.BorelProperQuotientStatement
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.HomogeneousQuotientProof
import Langlands.GroupScheme.ProjectiveOrbitRationalPoints
import Langlands.GroupScheme.FlagCoreLinear
import Langlands.GroupScheme.MatrixRepresentation.InvariantCoordinates
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Proper Borel quotients and closed projective orbits for the flag covering core -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.FlagCore

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The fibers of `q : G.X ⟶ Q` lie in left cosets of the subgroup `b : B ⟶ G`: on every test
scheme `V`, `g ≫ q = h ≫ q` implies `g⁻¹ * h ∈ range b`. -/
def FibersInCosets {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    {B : GroupScheme (Spec (CommRingCat.of k))} (b : B ⟶ G) : Prop :=
  ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
    g ≫ q = h ≫ q → g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier V

/-- The fibers of `q : G.X ⟶ Q` stabilize the line of `v` under the matrix representation `σ`:
on every test scheme `T`, `g ≫ q = h ≫ q` implies that `σ(g⁻¹ h)` maps the image `v_T` of `v` to
a unit multiple of `v_T`. -/
def FibersStabilizeLine {m : Type} [Fintype m] [DecidableEq m] (σ : MatrixRepresentation G m)
    (v : m → k) {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X), g ≫ q = h ≫ q →
    ∃ a : Γ(T.left, ⊤)ˣ,
      (σ.pointMatrix T (g⁻¹ * h) : Matrix m m Γ(T.left, ⊤)) *ᵥ (fun i => scalarMap T (v i)) =
        (a : Γ(T.left, ⊤)) • fun i => scalarMap T (v i)

/-- Right translation by a rational point is right multiplication by the constant point. -/
theorem comp_mulRight_hom (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    {V : Over (Spec (CommRingCat.of k))} (g : V ⟶ G.X) :
    g ≫ (GrpObj.mulRight (A := G.X) x).hom = g * G.constantPoint x V := by
  have h : CartesianMonoidalCategory.toUnit V ≫ x = G.constantPoint x V := by
    unfold constantPoint
    congr 1
  simp only [GrpObj.mulRight, Hom.mul_def, CartesianMonoidalCategory.comp_lift_assoc,
    Category.comp_id, CartesianMonoidalCategory.comp_toUnit_assoc, h]

/-- The scalar map of the base, followed by `Γ(Spec R) ≅ R`, is the identity. -/
theorem ΓSpecIso_hom_scalarMap (r : k) :
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom
      (scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k)))) r) = r := by
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    Scheme.Hom.appTop (𝟙 (Spec (CommRingCat.of k))) ≫
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom) r = r
  rw [Scheme.Hom.id_appTop, Category.id_comp, Iso.inv_hom_id]
  rfl

omit [Field k] in
/-- Replacing the column `i` of the identity matrix by `v` gives determinant `v i`. -/
theorem det_updateCol_one {k : Type*} [Field k] {m : Type} [Fintype m] [DecidableEq m]
    (v : m → k) (i : m) : (updateCol (1 : Matrix m m k) i v).det = v i := by
  rw [← cramer_apply, cramer_one]
  rfl

variable [IsAlgClosed k]

/-- **A proper quotient by a given Borel subgroup.**  Given that some Borel subgroup has proper
actual quotients and that Borel subgroups are conjugate, every Borel subgroup `b : B ⟶ G` admits a
smooth, surjective, quasi-compact morphism `q` from `G` onto a proper scheme whose fibers lie in
left cosets of `B`: `q` is right translation by the conjugating point followed by the quotient by
the proper Borel. -/
theorem exists_proper_quotient (hproper : SomeBorelQuotientProperStatement.{u})
    (hconj : BorelConjugacyStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {B : GroupScheme (Spec (CommRingCat.of k))} {b : B ⟶ G} (hb : IsBorelSubgroup b) :
    ∃ (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q),
      IsProper Q.hom ∧ Smooth q.left ∧ Surjective q.left ∧ QuasiCompact q.left ∧
        FibersInCosets q b := by
  obtain ⟨B₀, b₀, hb₀, hQ⟩ := hproper k G inferInstance
  obtain ⟨Q, q₀, hsep, hlft, hqc, hsm, hsurj, hqqc, hfib⟩ :=
    smoothSubgroupQuotientExistence k G B₀ b₀ hb₀.isClosedSubgroup hb₀.smooth
  obtain ⟨x, φ, hφ⟩ := (hconj k G).2 B₀ B b₀ b hb₀ hb
  let t := (GrpObj.mulRight (A := G.X) x).hom
  have : IsIso t.left := inferInstanceAs (IsIso ((Over.forget _).map t))
  refine ⟨Q, t ≫ q₀, hQ Q q₀ hsep hlft hqc hsm hsurj hqqc hfib, ?_, ?_, ?_, ?_⟩
  · change Smooth (t.left ≫ q₀.left)
    infer_instance
  · change Surjective (t.left ≫ q₀.left)
    infer_instance
  · change QuasiCompact (t.left ≫ q₀.left)
    infer_instance
  · intro V g h hgh
    have h1 : (g * G.constantPoint x V) ≫ q₀ = (h * G.constantPoint x V) ≫ q₀ := by
      rw [← comp_mulRight_hom, ← comp_mulRight_hom, Category.assoc, Category.assoc]
      exact hgh
    obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp ((hfib V _ _).mp h1)
    refine SubgroupFunctor.mem_range.mpr ⟨w ≫ φ.hom.hom.hom, ?_⟩
    have h2 : w ≫ b₀.hom.hom ≫ (G.innerIso x).hom.hom.hom = w ≫ φ.hom.hom.hom ≫ b.hom.hom := by
      have h3 := congrArg (fun f : B₀ ⟶ G => f.hom.hom) hφ
      simp only [Grp.comp_hom_hom] at h3
      rw [h3]
    rw [← Category.assoc, comp_innerIso_hom, hw] at h2
    rw [Category.assoc, ← h2]
    group

/-- **Closed orbits of lines with proper stabilizer quotients.**  Let `σ` be a matrix
representation of `G` and `v ≠ 0` a vector whose line is stabilized, on every test scheme, by the
fibers of a flat, surjective, quasi-compact morphism `q` from `G` onto a proper scheme.  Then the
orbit `g ↦ σ(g) v` of rational points is closed in the sense of homogeneous equations. -/
theorem isClosedOrbit_of_isProper [LocallyOfFiniteType G.X.hom]
    {m : Type} [Fintype m] [DecidableEq m] (σ : MatrixRepresentation G m) {v : m → k}
    (hv : v ≠ 0) {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left] [IsProper Q.hom]
    (hq : FibersStabilizeLine σ v q) :
    IsClosedOrbit fun g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X =>
      (σ.rationalMatrix g : Matrix m m k) *ᵥ v := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hv (funext hall)
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card m = N + 1 :=
    ⟨Fintype.card m - 1, (Nat.succ_pred_eq_of_pos (Fintype.card_pos_iff.mpr ⟨i₀⟩)).symm⟩
  -- Coordinates adapted to `v`: the columns of `A` are a basis whose `i₀`-th member is `v`.
  obtain ⟨e⟩ : Nonempty (Fin (N + 1) ≃ m) := ⟨(Fintype.equivFinOfCardEq hN).symm⟩
  obtain ⟨A, hA⟩ : ∃ A : Matrix m m k, A = updateCol 1 i₀ v := ⟨_, rfl⟩
  have hdet : IsUnit A.det := by
    rw [hA, det_updateCol_one]
    exact hi₀.isUnit
  have hAA : A⁻¹ * A = 1 := nonsing_inv_mul A hdet
  have hAA' : A * A⁻¹ = 1 := mul_nonsing_inv A hdet
  have hAcol : ∀ i, A i i₀ = v i := fun i => by rw [hA, updateCol_self]
  obtain ⟨Bm, hBm⟩ : ∃ Bm : Matrix m (Fin (N + 1)) k, Bm = A.submatrix id e := ⟨_, rfl⟩
  obtain ⟨Cm, hCm⟩ : ∃ Cm : Matrix (Fin (N + 1)) m k, Cm = A⁻¹.submatrix e id := ⟨_, rfl⟩
  have hCB : Cm * Bm = 1 := by
    rw [hCm, hBm, show (id : m → m) = Equiv.refl m from rfl, submatrix_mul_equiv, hAA,
      submatrix_one_equiv]
  have hBC : Bm * Cm = 1 := by
    rw [hCm, hBm, show (id : m → m) = Equiv.refl m from rfl, submatrix_mul_equiv, hAA']
    exact submatrix_one_equiv _
  set j₀ := e.symm i₀ with hj₀
  have hBcol : ∀ i, Bm i j₀ = v i := fun i => by
    rw [hBm, submatrix_apply, hj₀, Equiv.apply_symm_apply, id, hAcol]
  have hmapBC : ∀ T : Over (Spec (CommRingCat.of k)),
      Bm.map (scalarMap T) * Cm.map (scalarMap T) = 1 := fun T => by
    rw [← Matrix.map_mul, hBC, Matrix.map_one _ (map_zero _) (map_one _)]
  have hmapCB : ∀ T : Over (Spec (CommRingCat.of k)),
      Cm.map (scalarMap T) * Bm.map (scalarMap T) = 1 := fun T => by
    rw [← Matrix.map_mul, hCB, Matrix.map_one _ (map_zero _) (map_one _)]
  have hstable : σ.IsStableCoordinates Bm Cm := by
    intro T x
    simp only [← Matrix.mul_assoc, hmapBC, Matrix.one_mul]
  set σ' := MatrixRepresentation.restrictCoordinates σ Bm Cm hCB hstable with hσ'
  have hσ'pt : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
      (σ'.pointMatrix T x : Matrix (Fin (N + 1)) (Fin (N + 1)) Γ(T.left, ⊤)) =
        Cm.map (scalarMap T) * (σ.pointMatrix T x : Matrix m m Γ(T.left, ⊤)) *
          Bm.map (scalarMap T) := fun T x => by
    rw [hσ', MatrixRepresentation.restrictCoordinates_pointMatrix, MonoidHom.coe_toHomUnits]
    rfl
  -- The line of `e_{j₀}` is stabilized by the fibers of `q` in the new coordinates.
  have hq' : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X), g ≫ q = h ≫ q →
      ∃ a : Γ(T.left, ⊤)ˣ,
        (σ'.pointMatrix T (g⁻¹ * h) : Matrix (Fin (N + 1)) (Fin (N + 1)) Γ(T.left, ⊤)) *ᵥ
            Pi.single j₀ 1 =
          (a : Γ(T.left, ⊤)) • (Pi.single j₀ (1 : Γ(T.left, ⊤)) : Fin (N + 1) → Γ(T.left, ⊤)) := by
    intro T g h hgh
    obtain ⟨a, ha⟩ := hq T g h hgh
    refine ⟨a, ?_⟩
    set vT : m → Γ(T.left, ⊤) := fun i => scalarMap T (v i) with hvT
    have hB : Bm.map (scalarMap T) *ᵥ Pi.single j₀ 1 = vT := by
      funext i
      rw [mulVec_single_one, col_apply, map_apply, hBcol]
    rw [hσ'pt, ← mulVec_mulVec, hB, ← mulVec_mulVec, ha, mulVec_smul, ← hB, mulVec_mulVec,
      hmapCB, one_mulVec]
  have ho' : IsClosedOrbit fun g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X =>
      (σ'.rationalMatrix g : Matrix (Fin (N + 1)) (Fin (N + 1)) k) *ᵥ Pi.single j₀ 1 :=
    fun c hc hfc => ProjectiveOrbit.exists_eq_smul_orbit_of_isProper N σ' j₀ q hq' c hc hfc
  -- Rational matrices in the new coordinates.
  have hmap : ∀ {a b : Type} [Fintype a] [Fintype b] (M : Matrix a b k),
      (M.map (scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).map
        (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom = M := fun M => by
    ext i l
    exact ΓSpecIso_hom_scalarMap (M i l)
  have hrat : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      (σ'.rationalMatrix g : Matrix (Fin (N + 1)) (Fin (N + 1)) k) =
        Cm * (σ.rationalMatrix g : Matrix m m k) * Bm := by
    intro g
    change (σ'.pointMatrix _ g : Matrix (Fin (N + 1)) (Fin (N + 1))
      Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)).map
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom = _
    rw [hσ'pt, Matrix.map_mul, Matrix.map_mul, hmap, hmap]
    rfl
  have hBv : Bm *ᵥ Pi.single j₀ 1 = v := by
    funext i
    rw [mulVec_single_one, col_apply, hBcol]
  have hCe : ∀ w : m → k, (Cm *ᵥ w) ∘ e.symm = A⁻¹ *ᵥ w := fun w => by
    funext i
    simp only [Function.comp_apply, hCm, mulVec, dotProduct, submatrix_apply,
      Equiv.apply_symm_apply, id]
  have hfun : (fun g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X =>
      (σ.rationalMatrix g : Matrix m m k) *ᵥ v) = fun g =>
        A *ᵥ (((σ'.rationalMatrix g : Matrix (Fin (N + 1)) (Fin (N + 1)) k) *ᵥ
          Pi.single j₀ 1) ∘ e.symm) := by
    funext g
    rw [hrat, ← mulVec_mulVec, hBv, ← mulVec_mulVec, hCe, mulVec_mulVec, hAA', one_mulVec]
  rw [hfun]
  exact (ho'.reindex e.symm).mulVec A A⁻¹ hAA hAA'

end Langlands.GroupScheme.FlagCore
