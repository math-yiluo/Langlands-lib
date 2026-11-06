import Langlands.GroupScheme.Reductive.SteinbergBigCellStatement
import Langlands.GroupScheme.Reductive.SteinbergCovariantExhaustionStatement
import Langlands.GroupScheme.Reductive.CovariantConjugateTransport
import Langlands.GroupScheme.Reductive.CovariantTensorEmbedding
import Langlands.GroupScheme.Reductive.CellExhaustion
import Langlands.GroupScheme.Reductive.SteinbergCovariantReduction
import Langlands.GroupScheme.Reductive.SteinbergTensorReduction

/-! # Covariant exhaustion from big-cell and Steinberg data -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry WithConv
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AffineCoordinates

section Inverse

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffine G.X.left]

/-- Evaluation at a test point, as an algebra map out of the coordinate Hopf algebra. -/
abbrev pointHopfAlgHom (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) :
    hopfAlgebra G →ₐ[k] ((algΓ (CommRingCat.of k)).obj T).unop :=
  pointAlgebraHom G T g

/-- The product of test points is evaluated by the convolution product. -/
theorem toConv_pointHopfAlgHom_mul (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X) :
    toConv (pointHopfAlgHom G T (g * h)) =
      toConv (pointHopfAlgHom G T g) * toConv (pointHopfAlgHom G T h) := by
  rw [AlgHom.convMul_def]
  congr 1
  ext x
  have e1 := congrArg (fun F : algebra G →ₐ[CommRingCat.of k] _ => F x)
    (pointAlgebraHom_mul G T g h)
  have hc : AffineLinearEmbedding.comul (corepresentation G) x =
      Coalgebra.comul (R := k) (A := hopfAlgebra G) x :=
    LinearMap.congr_fun (corepresentation_comul G) x
  refine e1.trans ((congrArg (Algebra.TensorProduct.productMap (pointAlgebraHom G T g)
    (pointAlgebraHom G T h)) hc).trans ?_)
  rw [Algebra.TensorProduct.productMap_eq_comp_map]
  rfl

/-- The identity test point is evaluated by the convolution unit. -/
theorem toConv_pointHopfAlgHom_one (T : Over (Spec (CommRingCat.of k))) :
    toConv (pointHopfAlgHom G T 1) = 1 := by
  rw [AlgHom.convOne_def]
  congr 1
  ext x
  have e1 := congrArg (fun F : algebra G →ₐ[CommRingCat.of k] _ => F x)
    (pointAlgebraHom_one G T)
  have hc : AffineLinearEmbedding.counit (corepresentation G) x =
      Coalgebra.counit (R := k) (A := hopfAlgebra G) x :=
    LinearMap.congr_fun (corepresentation_counit G) x
  refine e1.trans ?_
  exact congrArg (Algebra.ofId k ((algΓ (CommRingCat.of k)).obj T).unop) hc

/-- The inverse of a test point is evaluated through the antipode. -/
theorem pointHopfAlgHom_inv (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) :
    pointHopfAlgHom G T g⁻¹ =
      (pointHopfAlgHom G T g).comp (HopfAlgebra.antipodeAlgHom k (hopfAlgebra G)) := by
  have hab : toConv (pointHopfAlgHom G T g) * toConv (pointHopfAlgHom G T g⁻¹) = 1 := by
    rw [← toConv_pointHopfAlgHom_mul, mul_inv_cancel, toConv_pointHopfAlgHom_one]
  have hs := Chevalley.antipode_convMul_self (pointHopfAlgHom G T g)
  apply WithConv.toConv_injective
  calc toConv (pointHopfAlgHom G T g⁻¹)
      = (toConv ((pointHopfAlgHom G T g).comp (HopfAlgebra.antipodeAlgHom k (hopfAlgebra G))) *
          toConv (pointHopfAlgHom G T g)) * toConv (pointHopfAlgHom G T g⁻¹) := by
        rw [hs, one_mul]
    _ = toConv ((pointHopfAlgHom G T g).comp
          (HopfAlgebra.antipodeAlgHom k (hopfAlgebra G))) := by
        rw [mul_assoc, hab, mul_one]

/-- The antipode of the coordinate Hopf algebra, as an algebra map of the coordinate
algebra. -/
abbrev antipodeCoord : algebra G →ₐ[k] algebra G :=
  HopfAlgebra.antipodeAlgHom k (hopfAlgebra G)

/-- Evaluating the antipode of a coordinate at a test point is evaluating the coordinate at
the inverse point. -/
theorem pointAlgebraHom_antipode (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X)
    (f : algebra G) :
    pointAlgebraHom G T g (antipodeCoord G f) =
      pointAlgebraHom G T g⁻¹ f :=
  (AlgHom.congr_fun (pointHopfAlgHom_inv G T g) f).symm

/-- Value one at the identity rational point means counit one. -/
theorem counit_eq_one_of_pointAlgebraHom_one (d : algebra G)
    (hd : pointAlgebraHom G (Over.mk (𝟙 (Spec (CommRingCat.of k)))) 1 d = 1) :
    Coalgebra.counit (R := k) (A := hopfAlgebra G) d = 1 := by
  have hc : AffineLinearEmbedding.counit (corepresentation G) d =
      Coalgebra.counit (R := k) (A := hopfAlgebra G) d :=
    LinearMap.congr_fun (corepresentation_counit G) d
  have : Nontrivial ((algΓ (CommRingCat.of k)).obj
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))).unop :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  apply (algebraMap k ((algΓ (CommRingCat.of k)).obj
    (Over.mk (𝟙 (Spec (CommRingCat.of k))))).unop).injective
  rw [map_one, ← hc, ← hd, pointAlgebraHom_one]
  rfl

end Inverse

section Covariant

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

local instance steinbergBigCellGlueInst1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance steinbergBigCellGlueInst2 : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

/-- Right covariance on all test schemes, `d(g i'(h)⁻¹) = χ(h) d(g)`, makes the antipode of
`d` left covariant for `i'` with the same weight. -/
theorem antipode_mem_leftCovariantSubspace_of_points (i' : H ⟶ G) (χ : algebra H)
    (d : algebra G)
    (hd : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (g : T ⟶ G.X),
      pointAlgebraHom G T (g * (h ≫ i'.hom.hom)⁻¹) d =
        pointAlgebraHom H T h χ * pointAlgebraHom G T g d) :
    antipodeCoord G d ∈ leftCovariantSubspace i' χ := by
  rw [mem_leftCovariantSubspace_iff_points]
  intro T h g
  rw [pointAlgebraHom_antipode, pointAlgebraHom_antipode, mul_inv_rev, hd]

end Covariant

section Adapter

open Chevalley.CellExhaustion

variable {k : Type u} [Field k]

/-- The spectrum counit of a `k`-algebra, as an algebra equivalence onto the global
functions of its spectrum. -/
def specCounitEquiv (B : CommAlgCat (CommRingCat.of k)) :
    B ≃ₐ[k] ((algΓ (CommRingCat.of k)).obj ((algSpec (CommRingCat.of k)).obj (op B))).unop :=
  AlgEquiv.ofBijective ((algΓAlgSpecAdjunction (CommRingCat.of k)).counit.app (op B)).unop.hom
    (by
      have : IsIso ((algΓAlgSpecAdjunction (CommRingCat.of k)).counit.app (op B)) := by
        have : (algSpec (CommRingCat.of k)).Full := algSpec.fullyFaithful.full
        have : (algSpec (CommRingCat.of k)).Faithful := algSpec.fullyFaithful.faithful
        infer_instance
      exact ConcreteCategory.bijective_of_isIso
        ((algΓAlgSpecAdjunction (CommRingCat.of k)).counit.app (op B)).unop)

/-- Pushing points forward along an injective algebra map is injective. -/
theorem postcomp_injective {A R R' : Type u} [CommRing A] [HopfAlgebra k A] [CommRing R]
    [Algebra k R] [CommRing R'] [Algebra k R'] {h : R →ₐ[k] R'} (hh : Function.Injective h) :
    Function.Injective (postcomp (A := A) h) := by
  intro X Y hXY
  apply WithConv.ofConv_injective
  ext a
  apply hh
  rw [← postcomp_ofConv_apply, ← postcomp_ofConv_apply, hXY]

variable (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

/-- A test point is determined by its evaluation of coordinates. -/
theorem pointAlgebraHom_injective (T : Over (Spec (CommRingCat.of k))) :
    Function.Injective (pointAlgebraHom G T) := by
  intro x y h
  rw [pointAlgebraHom_eq, pointAlgebraHom_eq] at h
  have h1 := ((algΓAlgSpecAdjunction (CommRingCat.of k)).homEquiv T
    (op (algebra G))).symm.injective (Quiver.Hom.unop_inj (CommAlgCat.hom_ext h))
  have h2 := congrArg (· ≫ (groupSchemeIso G).hom.hom.hom) h1
  have e : (groupSchemeIso G).inv.hom.hom ≫ (groupSchemeIso G).hom.hom.hom = 𝟙 _ :=
    congrArg (fun z => z.hom.hom) (groupSchemeIso G).inv_hom_id
  calc x = (x ≫ (groupSchemeIso G).inv.hom.hom) ≫ (groupSchemeIso G).hom.hom.hom := by
        rw [Category.assoc, e, Category.comp_id]
    _ = (y ≫ (groupSchemeIso G).inv.hom.hom) ≫ (groupSchemeIso G).hom.hom.hom := h2
    _ = y := by rw [Category.assoc, e, Category.comp_id]

/-- Evaluation at the point of the spectrum of `R` given by an algebra map. -/
theorem pointHopfAlgHom_algPoint {R : Type u} [CommRing R] [Algebra k R]
    (φ : hopfAlgebra G →ₐ[k] R) :
    pointHopfAlgHom G _ (algPoint G (CommAlgCat.ofHom φ)) =
      (specCounitEquiv (CommAlgCat.of (CommRingCat.of k) R)).toAlgHom.comp φ :=
  pointAlgebraHom_algPoint G _

variable {G}

section Hom

variable {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffine H.X.left]
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- Restricting an evaluated point along an actual homomorphism evaluates the composite. -/
theorem pointMap_toConv_pointHopfAlgHom (i : H ⟶ G) (T : Over (Spec (CommRingCat.of k)))
    (b : T ⟶ H.X) :
    pointMap (AffineHomImageHopfAdapter.pullback i).hom (toConv (pointHopfAlgHom H T b)) =
      toConv (pointHopfAlgHom G T (b ≫ i.hom.hom)) := by
  apply WithConv.ofConv_injective
  ext a
  rw [pointMap_ofConv_apply]
  exact (AlgHom.congr_fun (AffineHomImageHopfAdapter.pointAlgebraHom_pullback i T b) a).symm

/-- The decomposition of test points on the unit locus of `d` gives the decomposition of
algebra-valued points used by `Chevalley.CellExhaustion`. -/
theorem decomposition_algebraPoints (i i' : H ⟶ G) (d : algebra G)
    (hdec : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
      IsUnit (pointAlgebraHom G T g d) →
        ∃ b b' : T ⟶ H.X, g = (b ≫ i.hom.hom) * (b' ≫ i'.hom.hom)⁻¹)
    (R : Type u) [CommRing R] [Algebra k R] (g : WithConv (hopfAlgebra G →ₐ[k] R))
    (hg : IsUnit (g.ofConv d)) :
    ∃ b b', g * pointMap (AffineHomImageHopfAdapter.pullback i').hom b' =
      pointMap (AffineHomImageHopfAdapter.pullback i).hom b := by
  let B : CommAlgCat (CommRingCat.of k) := CommAlgCat.of (CommRingCat.of k) R
  let ε := specCounitEquiv B
  let x := algPoint G (CommAlgCat.ofHom g.ofConv)
  have hx : pointHopfAlgHom G _ x = ε.toAlgHom.comp g.ofConv := pointHopfAlgHom_algPoint G _
  have hu : IsUnit (pointAlgebraHom G _ x d) := by
    change IsUnit (pointHopfAlgHom G _ x d)
    rw [hx]
    exact hg.map ε.toAlgHom
  obtain ⟨b, b', hbb⟩ := hdec _ x hu
  refine ⟨toConv (ε.symm.toAlgHom.comp (pointHopfAlgHom H _ b)),
    toConv (ε.symm.toAlgHom.comp (pointHopfAlgHom H _ b')), ?_⟩
  have hεε : ∀ φ : hopfAlgebra H →ₐ[k] _,
      postcomp ε.toAlgHom (toConv (ε.symm.toAlgHom.comp φ)) = toConv φ := fun φ => by
    apply WithConv.ofConv_injective
    ext a
    exact ε.apply_symm_apply (φ a)
  apply postcomp_injective (A := hopfAlgebra G) (h := ε.toAlgHom) ε.injective
  rw [map_mul, postcomp_pointMap, postcomp_pointMap, hεε, hεε,
    pointMap_toConv_pointHopfAlgHom, pointMap_toConv_pointHopfAlgHom]
  have hg' : postcomp ε.toAlgHom g = toConv (pointHopfAlgHom G _ x) := by
    rw [hx]
    rfl
  rw [hg', ← toConv_pointHopfAlgHom_mul, hbb, inv_mul_cancel_right]

/-- Left invariance under `j` and the intersection condition give the invariance under
common points of `i` and `i'` used by `Chevalley.CellExhaustion`. -/
theorem intersection_algebraPoints {D : GroupScheme (Spec (CommRingCat.of k))}
    (j : D ⟶ G) (i i' : H ⟶ G) (w : algebra G)
    (hint : ∀ (T : Over (Spec (CommRingCat.of k))) (c c' : T ⟶ H.X),
      c ≫ i.hom.hom = c' ≫ i'.hom.hom → ∃ t : T ⟶ D.X, c ≫ i.hom.hom = t ≫ j.hom.hom)
    (hw : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ D.X) (g : T ⟶ G.X),
      pointAlgebraHom G T ((h ≫ j.hom.hom) * g) w = pointAlgebraHom G T g w)
    (R : Type u) [CommRing R] [Algebra k R] (c c' : WithConv (hopfAlgebra H →ₐ[k] R))
    (hcc : pointMap (AffineHomImageHopfAdapter.pullback i).hom c =
      pointMap (AffineHomImageHopfAdapter.pullback i').hom c')
    (g : WithConv (hopfAlgebra G →ₐ[k] R)) :
    (pointMap (AffineHomImageHopfAdapter.pullback i).hom c * g).ofConv w = g.ofConv w := by
  let B : CommAlgCat (CommRingCat.of k) := CommAlgCat.of (CommRingCat.of k) R
  let ε := specCounitEquiv B
  let cp := algPoint H (CommAlgCat.ofHom c.ofConv)
  let cp' := algPoint H (CommAlgCat.ofHom c'.ofConv)
  let gp := algPoint G (CommAlgCat.ofHom g.ofConv)
  have hc : toConv (pointHopfAlgHom G _ (cp ≫ i.hom.hom)) =
      postcomp ε.toAlgHom (pointMap (AffineHomImageHopfAdapter.pullback i).hom c) := by
    rw [← pointMap_toConv_pointHopfAlgHom, postcomp_pointMap, pointHopfAlgHom_algPoint]
    rfl
  have hc' : toConv (pointHopfAlgHom G _ (cp' ≫ i'.hom.hom)) =
      postcomp ε.toAlgHom (pointMap (AffineHomImageHopfAdapter.pullback i').hom c') := by
    rw [← pointMap_toConv_pointHopfAlgHom, postcomp_pointMap, pointHopfAlgHom_algPoint]
    rfl
  have hgp : toConv (pointHopfAlgHom G _ gp) = postcomp ε.toAlgHom g := by
    rw [pointHopfAlgHom_algPoint]
    rfl
  have heq : cp ≫ i.hom.hom = cp' ≫ i'.hom.hom := by
    apply pointAlgebraHom_injective G
    have h := hc.trans ((congrArg (postcomp ε.toAlgHom) hcc).trans hc'.symm)
    exact congrArg WithConv.ofConv h
  obtain ⟨t, ht⟩ := hint _ cp cp' heq
  apply ε.injective
  have e1 := congrArg (fun F => F.ofConv w) (map_mul (postcomp ε.toAlgHom)
    (pointMap (AffineHomImageHopfAdapter.pullback i).hom c) g)
  rw [← hc, ← hgp, ← toConv_pointHopfAlgHom_mul, ht] at e1
  refine e1.trans ?_
  change pointAlgebraHom G _ ((t ≫ j.hom.hom) * gp) w = _
  rw [hw]
  exact congrArg (fun F => F.ofConv w) hgp

end Hom

end Adapter

end AffineCoordinates

open AffineLinearEmbedding MatrixRepresentation

section Steinberg

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

local instance steinbergBigCellGlueInst3 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance steinbergBigCellGlueInst4 : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

/-- Cofinal irreducibility of the covariant coordinates of `i` gives, for the `n`-conjugate
of `i` and the same weights, bases of equal size. -/
theorem exists_conj_irreducible_bases (i : H ⟶ G)
    (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (χ : AffineCoordinates.algebra H)
    (hst : ∀ e : ℕ, ∃ e' : ℕ, e ≤ e' ∧ ∃ (m : ℕ)
      (bX : Module.Basis (Fin m) k (AffineCoordinates.leftCovariantSubspace i (χ ^ e'))),
      (Chevalley.affineRegularRepresentation G _ bX
        (fun f _ hv => AffineCoordinates.rightAct_mem_leftCovariantSubspace i (χ ^ e') f
          hv)).rationalRepresentation.IsIrreducible) :
    ∀ e : ℕ, ∃ e' : ℕ, e ≤ e' ∧ ∃ (m : ℕ)
      (bX : Module.Basis (Fin m) k (AffineCoordinates.leftCovariantSubspace i (χ ^ e')))
      (_ : Module.Basis (Fin m) k
        (AffineCoordinates.leftCovariantSubspace (i ≫ (G.innerIso n).hom) (χ ^ e')))
      (hX : letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
        ∀ (f : Module.Dual k (AffineCoordinates.algebra G))
          (v : AffineCoordinates.algebra G),
          v ∈ AffineCoordinates.leftCovariantSubspace i (χ ^ e') →
            rightAct f v ∈ AffineCoordinates.leftCovariantSubspace i (χ ^ e')),
      (Chevalley.affineRegularRepresentation G _ bX hX).rationalRepresentation.IsIrreducible := by
  intro e
  obtain ⟨e', he, m, bX, hirr⟩ := hst e
  exact ⟨e', he, m, bX, AffineCoordinates.leftCovariantConjBasis i n _ bX, _, hirr⟩

/-- Big-cell and Steinberg data imply covariant exhaustion by Steinberg-type products. -/
def SteinbergCovariantExhaustionFromBigCellStatement : Prop :=
  SteinbergBigCellStatement.{u} → SteinbergCovariantExhaustionStatement.{u}

open Chevalley.CellExhaustion in
/-- Proof of the reduction: the conjugate `i' = i ≫ inn(n)` with the same weight `χ` serves
as the second subgroup map, `Chevalley.CellExhaustion` supplies density, `1 ∈ X₁ Y₁` and
exhaustion after translating the hypotheses to algebra-valued points, and translation by
`n` supplies equal-size bases. -/
theorem steinbergCovariantExhaustion_of_bigCell :
    SteinbergCovariantExhaustionFromBigCellStatement.{u} := by
  intro hB k _ _ p _ _ G _ hG
  obtain ⟨Λ, _, j, H, _, i, n, χ, d, hd, hright, hone, hnzd, hdec, hint, hst⟩ :=
    hB k p G hG
  have hdH := hd
  rw [AffineCoordinates.leftCovariantSubspace_eq_hopf] at hdH
  have hd' := AffineCoordinates.antipode_mem_leftCovariantSubspace_of_points
    (i ≫ (G.innerIso n).hom) χ d hright
  rw [AffineCoordinates.leftCovariantSubspace_eq_hopf] at hd'
  have hε := AffineCoordinates.counit_eq_one_of_pointAlgebraHom_one G d hone
  have hdec' := AffineCoordinates.decomposition_algebraPoints i (i ≫ (G.innerIso n).hom) d hdec
  have hreg : IsLeftRegular (d : AffineCoordinates.hopfAlgebra G) :=
    (isRegular_iff_mem_nonZeroDivisors.mpr hnzd).left
  refine ⟨Λ, inferInstance, j, H, H, inferInstance, inferInstance, i,
    i ≫ (G.innerIso n).hom, χ, χ, ?_, ?_, ?_,
    exists_conj_irreducible_bases i n χ hst⟩
  · exact injective_differenceComorphism (AffineHomImageHopfAdapter.pullback i).hom
      (AffineHomImageHopfAdapter.pullback (i ≫ (G.innerIso n).hom)).hom hdec' hreg
  · rw [AffineCoordinates.leftCovariantSubspace_eq_hopf,
      AffineCoordinates.leftCovariantSubspace_eq_hopf]
    exact one_mem_mul_leftCovariantSubspace (AffineHomImageHopfAdapter.pullback i).hom
      (AffineHomImageHopfAdapter.pullback (i ≫ (G.innerIso n).hom)).hom hdH hd' hε
  · intro w hw
    obtain ⟨N, hN⟩ := exists_mem_mul_leftCovariantSubspace
      (AffineHomImageHopfAdapter.pullback i).hom
      (AffineHomImageHopfAdapter.pullback (i ≫ (G.innerIso n).hom)).hom hdH hd' hε hdec'
      (AffineCoordinates.intersection_algebraPoints j i (i ≫ (G.innerIso n).hom) w hint hw)
    refine ⟨N, ?_⟩
    rw [AffineCoordinates.leftCovariantSubspace_eq_hopf,
      AffineCoordinates.leftCovariantSubspace_eq_hopf]
    exact hN

/-- Big-cell and Steinberg data imply the simply connected positive-characteristic
conjugation-map statement, through covariant exhaustion and Steinberg tensor embeddings. -/
theorem simplyConnectedPositiveCharConjugationMap_of_bigCell
    (h : SteinbergBigCellStatement.{u}) :
    SimplyConnectedPositiveCharConjugationMapStatement.{u} :=
  simplyConnectedPositiveCharConjugationMap_of_steinberg
    (steinbergTensorEmbedding_of_covariantExhaustion (steinbergCovariantExhaustion_of_bigCell h))

end Steinberg

end Langlands.GroupScheme
