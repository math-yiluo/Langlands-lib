import Langlands.GroupScheme.Dynamic.GeneralLinearCell
import Langlands.GroupScheme.Dynamic.GeneralLinearStabilizer
import Langlands.GroupScheme.Dynamic.GeneralLinearOrbit
import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Langlands.GroupScheme.Dynamic.OppositeIntersection

/-! # The opposite open cell of a closed subgroup of `GL_n` with diagonal cocharacter

Let `G` be an affine group scheme over a field `k`, `ρ : G → GL_n` a closed subgroup and
`χ : 𝔾_m → G` a cocharacter with `χ ≫ ρ = diag(t ^ e i)`. If `iU : U → G` represents `U(χ⁻¹)`
and `iP : P → G` represents `P(χ)`, the multiplication `U ×_k P → G` is an open immersion.

The image of the multiplication lies in the basic open `Ω` of `G` where the cell minor of `ρ`
is invertible. On `Ω`, the matrix of the inclusion `Ω → G → GL_n` factors as `u p` in the
block cell of `GL_n`, and the stabilizer argument of `GeneralLinearStabilizer` shows that `p`
comes from `G`. This gives a section `Ω → U ×_k P` of the multiplication, which is a
monomorphism because `U(χ⁻¹)` and `P(χ)` meet trivially.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite MvPolynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A global section whose basic open is the whole scheme is a unit. -/
theorem isUnit_of_basicOpen_eq_top {X : Scheme.{u}} {r : Γ(X, ⊤)} (h : X.basicOpen r = ⊤) :
    IsUnit r :=
  X.toLocallyRingedSpace.toRingedSpace.isUnit_of_isUnit_germ ⊤ r fun x _ =>
    (X.mem_basicOpen_top r x).1 (by rw [h]; trivial)

namespace GeneralLinear

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]

/-- The global sections of a scheme over `Spec k`, as a `k`-algebra through the structure map. -/
local instance sectionsAlgebra (T : Over (Spec (CommRingCat.of k))) : Algebra k Γ(T.left, ⊤) :=
  ((algΓ (CommRingCat.of k)).obj T).unop.algebra

/-- A polynomial in the matrix coordinates, evaluated at the matrix of a point `y` of `GL_n`,
is the pullback along `y` of the corresponding global function on `GL_n`. -/
theorem aeval_values_pointsEquiv (T : Over (Spec (CommRingCat.of k)))
    (y : T ⟶ (groupScheme n (CommRingCat.of k)).X) (f : MvPolynomial (Coordinate n) k) :
    aeval (values (pointsEquiv n _ T y)) f =
      y.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing n (CommRingCat.of k)))).inv
        (quotient n (CommRingCat.of k) f)) := by
  rw [← adjunction_homEquiv_symm_apply, pointsEquiv_apply]
  exact (classify_quotient _ f).symm.trans (DFunLike.congr_fun (classify_point _) _)

/-- Precomposing the diagonal cocharacter of `e` with inversion gives that of `-e`. -/
theorem inv_comp_diagonalCocharacter (e : n → ℤ) :
    CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
        diagonalCocharacter n (CommRingCat.of k) e =
      diagonalCocharacter n (CommRingCat.of k) (-e) := by
  refine hom_ext_points fun T x => ?_
  apply (pointsEquiv n _ T).injective
  rw [Grp.comp_hom_hom, ← Category.assoc, Gm.powerHom_apply, Gm.comp_zsmul_id,
    pointsEquiv_diagonalCocharacter, pointsEquiv_diagonalCocharacter, map_zpow, zpow_neg_one]
  ext i j
  simp only [coe_diagonalUnits, Matrix.diagonal_apply, Pi.neg_apply, inv_zpow', zpow_neg]

end GeneralLinear

namespace Dynamic

open _root_.Langlands.GroupScheme.GeneralLinear

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]
  {G : GroupScheme (Spec (CommRingCat.of k))} (ρ : G ⟶ groupScheme n (CommRingCat.of k))

local instance sectionsAlgebra (T : Over (Spec (CommRingCat.of k))) : Algebra k Γ(T.left, ⊤) :=
  ((algΓ (CommRingCat.of k)).obj T).unop.algebra

/-- The equations of `G` in `GL_n`: the polynomials in the matrix coordinates vanishing on the
matrix of the universal point of `G`. -/
def embeddingIdeal : Ideal (MvPolynomial (Coordinate n) k) :=
  RingHom.ker (aeval (R := k) (values (pointsEquiv n _ G.X ρ.hom.hom)))

variable {ρ}

/-- The image in `GL_n` of every point of `G` is a zero of the equations of `G`. -/
theorem pointsEquiv_comp_mem_zeroLocus {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ G.X) :
    pointsEquiv n _ T (x ≫ ρ.hom.hom) ∈ zeroLocus Γ(T.left, ⊤) (embeddingIdeal ρ) := by
  intro f hf
  have h := RingHom.mem_ker.mp hf
  rw [aeval_values_pointsEquiv] at h ⊢
  change x.left.appTop (ρ.hom.hom.left.appTop _) = 0
  rw [h, map_zero]

/-- For a closed subgroup, a point of `GL_n` whose matrix is a zero of the equations of `G`
comes from a point of `G`. -/
theorem exists_comp_eq_of_mem_zeroLocus [IsClosedImmersion ρ.hom.hom.left]
    {T : Over (Spec (CommRingCat.of k))} (y : T ⟶ (groupScheme n (CommRingCat.of k)).X)
    (hy : pointsEquiv n _ T y ∈ zeroLocus Γ(T.left, ⊤) (embeddingIdeal ρ)) :
    ∃ x : T ⟶ G.X, x ≫ ρ.hom.hom = y := by
  have : IsAffine (groupScheme n (CommRingCat.of k)).X.left := isAffine_groupScheme n _
  have hle : ρ.hom.hom.left.ker ≤ y.left.ker := by
    rw [Scheme.ker_of_isAffine, Scheme.ker_of_isAffine]
    intro U
    refine Ideal.map_mono fun s hs => ?_
    obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective
      ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing n (CommRingCat.of k)))).hom s)
    have hs' : s = (Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing n (CommRingCat.of k)))).inv
        (quotient n (CommRingCat.of k) f) := by
      rw [quotient, Ideal.Quotient.mkₐ_eq_mk, hf]
      exact (CategoryTheory.Iso.hom_inv_id_apply _ s).symm
    rw [RingHom.mem_ker, hs'] at hs ⊢
    rw [← aeval_values_pointsEquiv] at hs ⊢
    exact hy f hs
  refine ⟨Over.homMk (IsClosedImmersion.lift ρ.hom.hom.left y.left hle) ?_, ?_⟩
  · rw [← Over.w ρ.hom.hom, ← Category.assoc, IsClosedImmersion.lift_fac, Over.w y]
  · exact Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ _)

variable (k) in
/-- The `k`-algebra `S` regarded through the global sections of its spectrum over `Spec k`. -/
abbrev affineTest (S : Type u) [CommRing S] [Algebra k S] : Over (Spec (CommRingCat.of k)) :=
  (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k S : CommAlgCat (CommRingCat.of k)))

variable (k) in
/-- The algebra `S` is the algebra of global sections of its spectrum. -/
def affineTestEquiv (S : Type u) [CommRing S] [Algebra k S] :
    S ≃ₐ[k] Γ((affineTest k S).left, ⊤) :=
  (Corepresented.affineSectionsAlgEquiv (R := CommRingCat.of k) (CommAlgCat.of k S)).symm

/-- Over an arbitrary `k`-algebra `S`, the zeros of the equations of a closed subgroup `G` in
`GL_n(S)` are the matrices of the points of `G` over `Spec S`. -/
theorem mem_zeroLocus_iff [IsClosedImmersion ρ.hom.hom.left] {S : Type u} [CommRing S]
    [Algebra k S] (g : GL n S) :
    g ∈ zeroLocus S (embeddingIdeal ρ) ↔ ∃ x : affineTest k S ⟶ G.X,
      pointsEquiv n _ _ (x ≫ ρ.hom.hom) =
        Matrix.GeneralLinearGroup.map (affineTestEquiv k S).toAlgHom.toRingHom g := by
  constructor
  · intro hg
    obtain ⟨x, hx⟩ := exists_comp_eq_of_mem_zeroLocus ((pointsEquiv n _ (affineTest k S)).symm
      (Matrix.GeneralLinearGroup.map (affineTestEquiv k S).toAlgHom.toRingHom g))
      (by rw [MulEquiv.apply_symm_apply]; exact map_mem_zeroLocus _ hg)
    exact ⟨x, by rw [hx, MulEquiv.apply_symm_apply]⟩
  · rintro ⟨x, hx⟩
    have h := map_mem_zeroLocus (affineTestEquiv k S).symm.toAlgHom
      (pointsEquiv_comp_mem_zeroLocus (ρ := ρ) x)
    rw [hx, ← Matrix.GeneralLinearGroup.map_comp_apply] at h
    convert h
    ext i j
    simp

/-- The polynomials of the ideal of `GL_n` vanish on the universal point of `G`. -/
theorem ideal_le_embeddingIdeal : ideal n k ≤ embeddingIdeal ρ := by
  intro f hf
  rw [embeddingIdeal, RingHom.mem_ker, ← classify_quotient, quotient, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]

/-- For a closed subgroup, the zero loci of its equations are closed under multiplication. -/
theorem zeroLocusMulClosed_embeddingIdeal [IsClosedImmersion ρ.hom.hom.left] :
    ZeroLocusMulClosed (embeddingIdeal ρ) := by
  intro R _ _ g h hg hh
  obtain ⟨x, hx⟩ := (mem_zeroLocus_iff (ρ := ρ) g).1 hg
  obtain ⟨y, hy⟩ := (mem_zeroLocus_iff (ρ := ρ) h).1 hh
  exact (mem_zeroLocus_iff (ρ := ρ) (g * h)).2
    ⟨x * y, by rw [MonObj.mul_comp, pointsEquiv_mul, hx, hy, map_mul]⟩

/-- The identity matrix is a zero of the equations of a closed subgroup. -/
theorem one_mem_zeroLocus_embeddingIdeal [IsClosedImmersion ρ.hom.hom.left] :
    (1 : GL n k) ∈ zeroLocus k (embeddingIdeal ρ) :=
  (mem_zeroLocus_iff (ρ := ρ) 1).2 ⟨1, by rw [MonObj.one_comp, pointsEquiv_one, map_one]⟩

variable {χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G} {e : n → ℤ}

/-- If `χ ≫ ρ` is the diagonal cocharacter of `e`, then `diag(T ^ e i)` over the Laurent
polynomials is a zero of the equations of `G`. -/
theorem diagonalUnits_mem_zeroLocus_embeddingIdeal [IsClosedImmersion ρ.hom.hom.left]
    (hχ : χ ≫ ρ = diagonalCocharacter n (CommRingCat.of k) e) :
    diagonalUnits (LaurentPolynomial k) e (unitT k) ∈
      zeroLocus (LaurentPolynomial k) (embeddingIdeal ρ) := by
  refine (mem_zeroLocus_iff (ρ := ρ) _).2 ⟨(Gm.pointsEquiv _ _).symm
    (Units.map (affineTestEquiv k (LaurentPolynomial k)).toAlgHom.toRingHom.toMonoidHom
      (unitT k)) ≫ χ.hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, hχ, pointsEquiv_diagonalCocharacter,
    MulEquiv.apply_symm_apply, map_diagonalUnits]

/-- Points of `U(χ⁻¹)` in terms of matrices, when `χ ≫ ρ` is the diagonal cocharacter of `e`. -/
theorem mem_unipotent_iff_of_diagonal [IsClosedImmersion ρ.hom.hom.left]
    (hχ : χ ≫ ρ = diagonalCocharacter n (CommRingCat.of k) e)
    {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ G.X) :
    x ∈ (unipotent (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
        χ)).carrier T ↔
      pointsEquiv n _ T (x ≫ ρ.hom.hom) ∈ blockUnipotentSubgroup Γ(T.left, ⊤) (-e) := by
  rw [unipotent_eq_comap_of_isClosedSubgroup _ ρ ‹_›, SubgroupFunctor.mem_comap, Category.assoc,
    hχ, inv_comp_diagonalCocharacter, unipotent_diagonalCocharacter]
  rfl

/-- Points of `P(χ)` in terms of matrices, when `χ ≫ ρ` is the diagonal cocharacter of `e`. -/
theorem mem_parabolic_iff_of_diagonal [IsClosedImmersion ρ.hom.hom.left]
    (hχ : χ ≫ ρ = diagonalCocharacter n (CommRingCat.of k) e)
    {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ G.X) :
    x ∈ (parabolic χ).carrier T ↔
      pointsEquiv n _ T (x ≫ ρ.hom.hom) ∈ blockParabolicSubgroup Γ(T.left, ⊤) e := by
  rw [parabolic_eq_comap_of_isClosedSubgroup _ ρ ‹_›, SubgroupFunctor.mem_comap, hχ,
    parabolic_diagonalCocharacter]
  rfl

/-- The pullback of the cell minor of the universal matrix of `G` along a point `z` is the cell
minor of the matrix of `z`. -/
theorem appTop_cellMinor {T : Over (Spec (CommRingCat.of k))} (z : T ⟶ G.X) :
    z.left.appTop (cellMinor e (pointsEquiv n _ G.X ρ.hom.hom : Matrix n n Γ(G.X.left, ⊤))) =
      cellMinor e (pointsEquiv n _ T (z ≫ ρ.hom.hom) : Matrix n n Γ(T.left, ⊤)) := by
  rw [pointsEquiv_naturality, map_cellMinor]
  rfl

/-- **The opposite open cell of a closed subgroup of `GL_n` with diagonal cocharacter.** If
`χ ≫ ρ` is the diagonal cocharacter of `e`, `iU` represents `U(χ⁻¹)`, `iP` represents `P(χ)` and
the multiplication `U ×_k P → G` is a monomorphism, then it is an open immersion. -/
theorem isOpenImmersion_mul_of_diagonal [IsClosedImmersion ρ.hom.hom.left]
    (hχ : χ ≫ ρ = diagonalCocharacter n (CommRingCat.of k) e)
    {U P : GroupScheme (Spec (CommRingCat.of k))} {iU : U ⟶ G} {iP : P ⟶ G}
    (hU : (unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)).IsRepresentedBy iU)
    (hP : (parabolic χ).IsRepresentedBy iP)
    (hm : Mono ((fst U.X P.X ≫ iU.hom.hom) * (snd U.X P.X ≫ iP.hom.hom))) :
    IsOpenImmersion ((fst U.X P.X ≫ iU.hom.hom) * (snd U.X P.X ≫ iP.hom.hom)).left := by
  set m := (fst U.X P.X ≫ iU.hom.hom) * (snd U.X P.X ≫ iP.hom.hom) with hm_def
  have hmemU {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ U.X) :
      pointsEquiv n _ T ((x ≫ iU.hom.hom) ≫ ρ.hom.hom) ∈
        blockUnipotentSubgroup Γ(T.left, ⊤) (-e) := by
    rw [← mem_unipotent_iff_of_diagonal hχ, ← hU.2]
    exact SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
  have hmemP {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ P.X) :
      pointsEquiv n _ T ((x ≫ iP.hom.hom) ≫ ρ.hom.hom) ∈
        blockParabolicSubgroup Γ(T.left, ⊤) e := by
    rw [← mem_parabolic_iff_of_diagonal hχ, ← hP.2]
    exact SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
  -- the basic open `Ω` of `G` where the cell minor is invertible
  set c : Γ(G.X.left, ⊤) :=
    cellMinor e (pointsEquiv n _ G.X ρ.hom.hom : Matrix n n Γ(G.X.left, ⊤)) with hc
  set Ω : G.X.left.Opens := G.X.left.basicOpen c with hΩ
  have hpre : m.left ⁻¹ᵁ Ω = ⊤ := by
    rw [hΩ, Scheme.preimage_basicOpen_top, hc, appTop_cellMinor]
    apply Scheme.basicOpen_of_isUnit
    rw [hm_def, MonObj.mul_comp, pointsEquiv_mul]
    exact isUnit_cellMinor_mul e (hmemU _) (hmemP _)
  have hrange : Set.range m.left ⊆ Set.range Ω.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change x ∈ m.left ⁻¹ᵁ Ω
    rw [hpre]
    trivial
  set l := IsOpenImmersion.lift Ω.ι m.left hrange with hl
  have hlfac : l ≫ Ω.ι = m.left := IsOpenImmersion.lift_fac _ _ _
  -- the inclusion of `Ω` as a point of `G`, and its cell decomposition
  let TΩ : Over (Spec (CommRingCat.of k)) := Over.mk (Ω.ι ≫ G.X.hom)
  let xΩ : TΩ ⟶ G.X := Over.homMk Ω.ι rfl
  have hunit : IsUnit (cellMinor e (pointsEquiv n _ TΩ (xΩ ≫ ρ.hom.hom) :
      Matrix n n Γ(TΩ.left, ⊤))) := by
    rw [← appTop_cellMinor]
    apply isUnit_of_basicOpen_eq_top
    change TΩ.left.basicOpen (Ω.ι.appTop c) = ⊤
    rw [← Scheme.preimage_basicOpen_top, ← hΩ]
    exact Scheme.Opens.ι_preimage_self Ω
  obtain ⟨u', hu', p', hp', hup⟩ := exists_cell_decomposition e _ hunit
  have hp'Z : p' ∈ zeroLocus Γ(TΩ.left, ⊤) (embeddingIdeal ρ) :=
    mem_zeroLocus_of_mul_mem e ideal_le_embeddingIdeal zeroLocusMulClosed_embeddingIdeal
      one_mem_zeroLocus_embeddingIdeal (diagonalUnits_mem_zeroLocus_embeddingIdeal hχ) hu' hp'
      (hup ▸ pointsEquiv_comp_mem_zeroLocus xΩ)
  obtain ⟨p₀, hp₀⟩ := exists_comp_eq_of_mem_zeroLocus ((pointsEquiv n _ TΩ).symm p')
    (by rw [MulEquiv.apply_symm_apply]; exact hp'Z)
  have hp₀P : p₀ ∈ (parabolic χ).carrier TΩ := by
    rw [mem_parabolic_iff_of_diagonal hχ, hp₀, MulEquiv.apply_symm_apply]
    exact hp'
  have hu₀U : xΩ * p₀⁻¹ ∈ (unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)).carrier TΩ := by
    rw [mem_unipotent_iff_of_diagonal hχ, MonObj.mul_comp, GrpObj.inv_comp, pointsEquiv_mul,
      map_inv, hp₀, MulEquiv.apply_symm_apply, hup, mul_inv_cancel_right]
    exact hu'
  rw [← hP.2] at hp₀P
  rw [← hU.2] at hu₀U
  obtain ⟨p₁, hp₁⟩ := SubgroupFunctor.mem_range.mp hp₀P
  obtain ⟨u₁, hu₁⟩ := SubgroupFunctor.mem_range.mp hu₀U
  -- the section `Ω → U ×_k P` of the multiplication
  set ψ : TΩ ⟶ U.X ⊗ P.X := lift u₁ p₁ with hψ
  have hψm : ψ ≫ m = xΩ := by
    rw [hm_def, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, lift_fst, lift_snd, hu₁,
      hp₁, inv_mul_cancel_right]
  have hψm' : ψ.left ≫ m.left = Ω.ι := by
    rw [← Over.comp_left, hψm]
    rfl
  have : IsIso l := ⟨ψ.left, by
    rw [← cancel_mono m.left, Category.assoc, hψm', hlfac, Category.id_comp], by
    rw [← cancel_mono Ω.ι, Category.assoc, hlfac, hψm', Category.id_comp]⟩
  rw [← hlfac]
  infer_instance

end Dynamic

end Langlands.GroupScheme
