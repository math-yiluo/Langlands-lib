import Langlands.GroupScheme.SplitExistence.Centralizer
import Langlands.GroupScheme.SplitExistence.Retraction
import Langlands.GroupScheme.SplitExistence.OrderedProduct
import Langlands.GroupScheme.Lie.DualNumberKernel
import Langlands.GroupScheme.GeneralLinearDualNumber

/-! # The Lie algebra of the dynamic unipotent subgroup

For the Chevalley group `G ⊆ GL_n` and its regular cocharacter `λ`, the morphism
`Φ : GL_n → GL_n, g ↦ ∏_{γ > 0} x_γ(r_γ(g))` built from the polynomial retraction `r` restricts
to the identity on `U_G(λ)`. On geometric points this is the ordered product decomposition of
`U⁺(K)`, and reducedness of `U_G(λ)` gives the identity of morphisms. Evaluating at dual numbers,
every element of `Lie U_G(λ)` is a linear combination of the root operators `e_γ`, `γ > 0`. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  (D : ChevalleyData P b)

section OrderedProductGL

variable {R : Type u} [CommRing R]

/-- The ordered product `∏_{j ∈ l} x_j(c j)` in `GL_n(R)`, for any commutative ring. -/
def opmGL (l : List J) (c : J → R) : GL (Fin D.n) R := (l.map fun j => D.x j (c j)).prod

theorem coe_opmGL (l : List J) (c : J → R) :
    (D.opmGL l c : Matrix (Fin D.n) (Fin D.n) R) = D.opm l c := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [opmGL, List.map_cons, List.prod_cons, Units.val_mul, ← opmGL, ih, opm_cons, coe_x]
    rfl

theorem opmGL_map {R' : Type u} [CommRing R'] (f : R →+* R') (l : List J) (c : J → R) :
    Matrix.GeneralLinearGroup.map f (D.opmGL l c) = D.opmGL l (f ∘ c) := by
  rw [opmGL, map_list_prod, List.map_map, opmGL]
  congr 1
  apply List.map_congr_left
  intro j _
  exact D.x_map f j (c j)

theorem opm_congr {l : List J} {c c' : J → R} (h : ∀ j ∈ l, c j = c' j) :
    D.opm l c = D.opm l c' := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [opm_cons, opm_cons, h j (List.mem_cons_self ..),
      ih fun j' hj' => h j' (List.mem_cons_of_mem _ hj')]

end OrderedProductGL

variable [Fintype J] [DecidableEq J]

/-- **Recovery on `U⁺(K)`.** Over a field `K` with a `k`-algebra structure, an element of `Γ(K)`
which is block unitriangular for the weights `ℓ(wt c)` is the ordered product of its recovered
coefficients. -/
theorem opm_retr_of_blockUnipotent [P.IsReduced] {k K : Type u} [Field k] [Field K]
    [Algebra k K] {g : GL (Fin D.n) K} (hg : g ∈ D.chevSub K)
    (hu : ∀ c d, D.ℓ (D.wt c) ≤ D.ℓ (D.wt d) →
      (g : Matrix (Fin D.n) (Fin D.n) K) c d = (1 : Matrix (Fin D.n) (Fin D.n) K) c d) :
    D.opm D.posList (D.retr k (g : Matrix (Fin D.n) (Fin D.n) K)) = g := by
  have hbt : g ∈ D.btSub K := fun c d hcd => by
    have hlt := OrderDual.toDual_lt_toDual.mp hcd
    rw [hu c d hlt.le, Matrix.one_apply_ne]
    rintro rfl
    exact lt_irrefl _ hlt
  have hB : g ∈ D.borelSub K := by
    rw [← D.chevSub_inf_btSub]
    exact ⟨hg, hbt⟩
  obtain ⟨τ, hτ, v, hv, rfl⟩ := mem_borelSub.1 hB
  obtain ⟨χ, rfl⟩ := hτ
  have hut : D.IsUT (v : Matrix (Fin D.n) (Fin D.n) K) := D.posSub_le_utSub hv
  have hdiag : ∀ c, ((χ (Multiplicative.ofAdd (D.wt c)) : Kˣ) : K) *
      (v : Matrix (Fin D.n) (Fin D.n) K) c c = 1 := by
    intro c
    have h := hu c c le_rfl
    rw [Units.val_mul, coe_torusHom, Matrix.diagonal_mul, Matrix.one_apply_eq] at h
    exact h
  have hχ : ∀ c, ((χ (Multiplicative.ofAdd (D.wt c)) : Kˣ) : K) = 1 := by
    intro c
    have hvc : (v : Matrix (Fin D.n) (Fin D.n) K) c c ≠ 0 := by
      intro h0
      have := hdiag c
      rw [h0, mul_zero] at this
      exact zero_ne_one this
    rcases hut c c hvc with ⟨-, h1⟩ | h
    · have := hdiag c
      rwa [h1, mul_one] at this
    · exact absurd h (lt_irrefl _)
  have hτ1 : D.torusHom χ = 1 := by
    ext c d
    rw [coe_torusHom, Units.val_one, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs with h
    · exact hχ c
    · rfl
  rw [hτ1, one_mul] at *
  obtain ⟨c, hc⟩ := D.exists_orderedProd_of_mem_posSub hv
  have hcoe : (v : Matrix (Fin D.n) (Fin D.n) K) = D.opm D.posList c := by
    rw [hc]
    exact D.coe_opmGL D.posList c
  rw [hcoe, retr_opm]
  exact D.opm_congr fun j hj => by simp [hj]

variable (k : Type u) [Field k]

/-- The coordinate algebra of `GL_n` over `k`. -/
abbrev coordAlg : CommAlgCat.{u} (CommRingCat.of k) :=
  GeneralLinear.coordinateAlgebra (Fin D.n) (CommRingCat.of k)

/-- The universal matrix: the identity point of `GL_n` in affine coordinates. -/
abbrev univMatrix : GL (Fin D.n) (D.coordAlg k) :=
  GeneralLinear.affinePointsEquiv (Fin D.n) (CommRingCat.of k) (D.coordAlg k) (𝟙 (D.GLk k).X)

/-- **The retraction morphism** `Φ : GL_n → GL_n`, `g ↦ ∏_{γ > 0} x_γ(r_γ(g))`. -/
def retrMor : (D.GLk k).X ⟶ (D.GLk k).X :=
  (GeneralLinear.affinePointsEquiv (Fin D.n) (CommRingCat.of k) (D.coordAlg k)).symm
    (D.opmGL D.posList (D.retr k (D.univMatrix k : Matrix (Fin D.n) (Fin D.n) (D.coordAlg k))))

/-- `Φ` on affine points: `Φ(g) = ∏_{γ > 0} x_γ(r_γ(g))`. -/
theorem affinePointsEquiv_retrMor (S : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op S) ⟶ (D.GLk k).X) :
    GeneralLinear.affinePointsEquiv (Fin D.n) (CommRingCat.of k) S (x ≫ D.retrMor k) =
      D.opmGL D.posList (D.retr k (GeneralLinear.affinePointsEquiv (Fin D.n) (CommRingCat.of k) S
        x : Matrix (Fin D.n) (Fin D.n) S)) := by
  set g := GeneralLinear.affinePointsEquiv (Fin D.n) (CommRingCat.of k) S x with hg
  let f : D.coordAlg k ⟶ S := CommAlgCat.ofHom (GeneralLinear.classify g)
  have hx : x = (algSpec (CommRingCat.of k)).map f.op := by
    rw [← GeneralLinear.affinePointsEquiv_symm_apply, hg, MulEquiv.symm_apply_apply]
  have hxg : GeneralLinear.affinePointsEquiv (Fin D.n) (CommRingCat.of k) S x =
      Matrix.GeneralLinearGroup.map f.hom.toRingHom (D.univMatrix k) := by
    conv_lhs => rw [hx, ← Category.comp_id ((algSpec (CommRingCat.of k)).map f.op)]
    exact GeneralLinear.affinePointsEquiv_naturality f (𝟙 _)
  have key : GeneralLinear.affinePointsEquiv (Fin D.n) (CommRingCat.of k) S
      ((algSpec (CommRingCat.of k)).map f.op ≫ D.retrMor k) =
      Matrix.GeneralLinearGroup.map f.hom.toRingHom
        (GeneralLinear.affinePointsEquiv (Fin D.n) (CommRingCat.of k) (D.coordAlg k)
          (D.retrMor k)) :=
    GeneralLinear.affinePointsEquiv_naturality f (D.retrMor k)
  have hmat : ((Matrix.GeneralLinearGroup.map f.hom.toRingHom (D.univMatrix k) : GL (Fin D.n) S) :
      Matrix (Fin D.n) (Fin D.n) S) =
      (D.univMatrix k : Matrix (Fin D.n) (Fin D.n) (D.coordAlg k)).map f.hom := by
    ext i j
    rfl
  rw [hx]
  refine key.trans ?_
  rw [retrMor, MulEquiv.apply_symm_apply, D.opmGL_map, hg, hxg, hmat, D.retr_map k f.hom]
  rfl

/-- The affine coordinates of a point of `GL_n` on an affine test scheme, and its global-section
coordinates, differ by the ring isomorphism `S ≅ Γ(Spec S)`. -/
def affSecEquiv (S : CommAlgCat.{u} (CommRingCat.of k)) :
    S ≃+* Γ(((algSpec (CommRingCat.of k)).obj (op S)).left, ⊤) :=
  (CommAlgCat.algEquivOfIso (Corepresented.affineSectionsIso S).symm).toRingEquiv

omit [Fintype J] [DecidableEq J] in
theorem pointsEquiv_eq_glMap (S : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op S) ⟶ (D.GLk k).X) :
    GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) _ x =
      glMapEquiv (affSecEquiv k S) (GeneralLinear.affinePointsEquiv (Fin D.n) _ S x) :=
  GeneralLinear.pointsEquiv_eq_affinePointsEquiv S x

omit [Fintype J] [DecidableEq J] in
theorem mem_chevPoints_iff_affine (S : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op S) ⟶ (D.GLk k).X) :
    x ∈ D.chevPoints k _ ↔ GeneralLinear.affinePointsEquiv (Fin D.n) _ S x ∈ D.chevSub S := by
  rw [mem_chevPoints, D.pointsEquiv_eq_glMap k S x]
  exact (D.mem_chevSub_iff_of_equiv (affSecEquiv k S)).symm

omit [Fintype J] [DecidableEq J] in
theorem pointsEquiv_apply_eq_affine (S : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op S) ⟶ (D.GLk k).X) (c d : Fin D.n) :
    (GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) _ x : Matrix (Fin D.n) (Fin D.n) _) c d =
      affSecEquiv k S ((GeneralLinear.affinePointsEquiv (Fin D.n) _ S x :
        Matrix (Fin D.n) (Fin D.n) S) c d) := by
  rw [D.pointsEquiv_eq_glMap k S x]
  rfl

namespace ChevGroup

variable {D k} (G : D.ChevGroup k)

/-- **`Φ` is the identity on `U_G(λ)`.** -/
theorem unipotent_retr [P.IsReduced] [IsAffine G.H.X.left] :
    (Dynamic.Affine.unipotentHom G.cochar).hom.hom ≫ G.i.hom.hom ≫ D.retrMor k =
      (Dynamic.Affine.unipotentHom G.cochar).hom.hom ≫ G.i.hom.hom := by
  have := G.smooth
  have := G.affine
  let χ := G.cochar
  let u := Dynamic.Affine.unipotentHom χ
  have hu := Dynamic.Affine.isRepresentedBy_unipotentHom χ
  have hus : Smooth (Dynamic.Affine.unipotentScheme χ).X.hom :=
    (dynamicSmooth k G.H χ _ u).2.2 hu
  have : IsReduced (Dynamic.Affine.unipotentScheme χ).X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _
      (Dynamic.Affine.unipotentScheme χ).X.hom
  have : LocallyOfFiniteType (Dynamic.Affine.unipotentScheme χ).X.hom := inferInstance
  have : IsAffineHom (D.GLk k).X.hom := GeneralLinear.isAffineHom_groupScheme _ _
  have : IsSeparated (D.GLk k).X.hom := IsSeparated.of_isAffineHom _
  let K := AlgebraicClosure k
  refine ext_of_extPoints K _ _ ?_
  intro pt
  have hy : pt ≫ u.hom.hom ∈ (Dynamic.unipotent χ).carrier (extPoint K) := by
    rw [← hu.2]
    exact ⟨pt, rfl⟩
  rw [Dynamic.unipotent_eq_comap_of_isClosedSubgroup χ G.i G.closed,
    SubgroupFunctor.mem_comap, G.cochar_comp_i,
    (GeneralLinear.dynamicStatement.1 (Fin D.n) (CommRingCat.of k) D.ellWeights).2.2,
    GeneralLinear.mem_blockUnipotent] at hy
  have hpts := G.points K (pt ≫ u.hom.hom)
  let S : CommAlgCat.{u} (CommRingCat.of k) := CommAlgCat.of k K
  let y : (algSpec (CommRingCat.of k)).obj (op S) ⟶ (D.GLk k).X := (pt ≫ u.hom.hom) ≫ G.i.hom.hom
  have ha1 : GeneralLinear.affinePointsEquiv (Fin D.n) _ S y ∈ D.chevSub K :=
    (D.mem_chevPoints_iff_affine k S y).1 hpts
  have ha2 : ∀ c d, D.ℓ (D.wt c) ≤ D.ℓ (D.wt d) →
      (GeneralLinear.affinePointsEquiv (Fin D.n) _ S y : Matrix (Fin D.n) (Fin D.n) K) c d =
        (1 : Matrix (Fin D.n) (Fin D.n) K) c d := by
    intro c d hcd
    apply (affSecEquiv k S).injective
    have h := hy c d hcd
    have h' := D.pointsEquiv_apply_eq_affine k S y c d
    rw [← h']
    refine h.trans ?_
    by_cases hcd' : c = d
    · subst hcd'
      simp only [Matrix.one_apply_eq, map_one]
      rfl
    · simp only [Matrix.one_apply_ne hcd', map_zero]
      rfl
  have key := D.opm_retr_of_blockUnipotent (k := k) ha1 ha2
  apply (GeneralLinear.affinePointsEquiv (Fin D.n) (CommRingCat.of k) S).injective
  change GeneralLinear.affinePointsEquiv (Fin D.n) _ S (y ≫ D.retrMor k) = _
  rw [D.affinePointsEquiv_retrMor k S y]
  apply Units.ext
  rw [D.coe_opmGL, key]
  rfl

open GeneralLinear.DualNumber in
/-- **Lie algebra of `U_G(λ)`.** The epsilon-coefficient matrix of an element of `Lie(G)` lying
in `U_G(λ)` is a linear combination of the root operators `e_γ`, `γ > 0`. -/
theorem coefficients_mem_span_of_unipotent [P.IsReduced] [IsAffine G.H.X.left]
    (x : lieKernel G.H k)
    (hx : x.val ∈ (Dynamic.unipotent G.cochar).carrier
      ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k (DualNumber k))))) :
    coefficients (GeneralLinear.affinePointsEquiv (Fin D.n) (CommRingCat.of k)
        (CommAlgCat.of k (DualNumber k)) (x.val ≫ G.i.hom.hom)) ∈
      Submodule.span k (Set.range fun j : {j : J // b.IsPos j} => D.eF (F := k) j) := by
  have := G.affine
  have hu := Dynamic.Affine.isRepresentedBy_unipotentHom G.cochar
  rw [← hu.2] at hx
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hx
  let S : CommAlgCat.{u} (CommRingCat.of k) := CommAlgCat.of k (DualNumber k)
  have hΦ : (x.val ≫ G.i.hom.hom) ≫ D.retrMor k = x.val ≫ G.i.hom.hom := by
    rw [← hy, Category.assoc, Category.assoc, Category.assoc, G.unipotent_retr]
  set a := GeneralLinear.affinePointsEquiv (Fin D.n) (CommRingCat.of k) S (x.val ≫ G.i.hom.hom)
    with ha
  have hopm : D.opmGL D.posList (D.retr k (a : Matrix (Fin D.n) (Fin D.n) S)) = a := by
    rw [ha, ← D.affinePointsEquiv_retrMor k S, hΦ]
  have hred : matrixReduction (Fin D.n) k a = 1 := by
    have hx1 : Lie.reduction G.H x.val = 1 := x.property
    have h1 := GeneralLinear.affinePointsEquiv_naturality
      (CommAlgCat.ofHom (TrivSqZeroExt.fstHom (CommRingCat.of k) k k) :
        S ⟶ CommAlgCat.of k k) (x.val ≫ G.i.hom.hom)
    rw [← Category.assoc] at h1
    change GeneralLinear.affinePointsEquiv (Fin D.n) _ _ (Lie.reduction G.H x.val ≫ G.i.hom.hom) =
      _ at h1
    rw [hx1, MonObj.one_comp, map_one] at h1
    exact h1.symm
  have hunit : matrixUnit (coefficients a) = a := matrixUnit_coefficients ⟨a, hred⟩
  apply D.mem_span_of_opm_retr
  have h2 := congrArg Units.val hopm
  simp only [D.coe_opmGL] at h2
  rw [← hunit, matrixUnit_val] at h2
  exact h2

end ChevGroup

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
