import Langlands.AlgebraicGeometry.Picard.FieldPicardInfinitesimalGluingStatement
import Langlands.AlgebraicGeometry.Picard.SquareGluingCech
import Langlands.AlgebraicGeometry.Picard.SquareGluingFullyFaithful
import Langlands.AlgebraicGeometry.Picard.InfinitesimalCartesianCube
import Langlands.AlgebraicGeometry.Picard.InfinitesimalLocalEffectivity
import Langlands.AlgebraicGeometry.Picard.LineBundleAffineTrivializingCover

/-! # Infinitesimal gluing for actual field Picard groupoids: proof -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

namespace SquareGluingDescent

open CubeMap InfinitesimalAffineOpenSquare

namespace Sq

variable (S : Sq.{u}) (U : S.X.Opens)

/-- The inverse-image square of an open subscheme of the total scheme. -/
@[simps]
def restrict : Sq.{u} where
  X₀ := (S.i₁ ≫ S.j₁) ⁻¹ᵁ U
  X₁ := S.j₁ ⁻¹ᵁ U
  X₂ := S.j₂ ⁻¹ᵁ U
  X := U
  i₁ := leftRestriction S.i₁ S.j₁ U
  i₂ := rightRestriction S.i₁ S.i₂ S.j₁ S.j₂ S.w U
  j₁ := S.j₁ ∣_ U
  j₂ := S.j₂ ∣_ U
  w := restriction_comm S.i₁ S.i₂ S.j₁ S.j₂ S.w U

/-- The inclusion cube of the inverse-image square of an open subscheme. -/
@[simps]
def restrictC : CubeMap S (S.restrict U) where
  t := U.ι
  g₁ := (S.j₁ ⁻¹ᵁ U).ι
  g₂ := (S.j₂ ⁻¹ᵁ U).ι
  g₀ := ((S.i₁ ≫ S.j₁) ⁻¹ᵁ U).ι
  h₁ := morphismRestrict_ι S.j₁ U
  h₂ := morphismRestrict_ι S.j₂ U
  k₁ := leftRestriction_ι S.i₁ S.j₁ U
  k₂ := rightRestriction_ι S.i₁ S.i₂ S.j₁ S.j₂ S.w U

instance : IsOpenImmersion (S.restrictC U).t := inferInstanceAs (IsOpenImmersion U.ι)

/-- The inclusion cube of an open subscheme is cartesian. -/
lemma cart_restrictC : (S.restrictC U).Cart := by
  refine ⟨(isPullback_morphismRestrict S.j₁ U).flip,
    (isPullback_morphismRestrict S.j₂ U).flip, ?_⟩
  have e : leftRestriction S.i₁ S.j₁ U = S.i₁ ∣_ (S.j₁ ⁻¹ᵁ U) :=
    Scheme.Hom.resLE_eq_morphismRestrict S.i₁
  change IsPullback ((S.i₁ ≫ S.j₁) ⁻¹ᵁ U).ι (leftRestriction S.i₁ S.j₁ U) S.i₁
    (S.j₁ ⁻¹ᵁ U).ι
  rw [e]
  exact (isPullback_morphismRestrict S.i₁ (S.j₁ ⁻¹ᵁ U)).flip

section Family

variable (V : S.X → S.X.Opens)

/-! Families indexed by points are named constants, not lambdas, so that the kernel
sees the binder types of `Cech.exists_iso` syntactically. -/

/-- The inverse-image squares of a family of opens. -/
def restrictFamily (x : S.X) : Sq.{u} := S.restrict (V x)

/-- The inclusion cubes of a family of opens. -/
def restrictCFamily (x : S.X) : CubeMap S (S.restrictFamily V x) := S.restrictC (V x)

/-- The trivial line bundles on a family of opens. -/
def trivialFamily (x : S.X) : PicardGroupoid (S.restrictFamily V x).X :=
  Core.mk (LineBundle.trivial (V x).toScheme)

instance (x : S.X) : IsOpenImmersion (S.restrictCFamily V x).t :=
  inferInstanceAs (IsOpenImmersion (V x).ι)

lemma cart_restrictCFamily (x : S.X) : (S.restrictCFamily V x).Cart :=
  S.cart_restrictC (V x)

/-- Inclusion cubes of opens containing their index points cover the total
scheme. -/
lemma restrictCFamily_cover (hV : ∀ x, x ∈ V x) :
    ∀ x : S.X, ∃ i y, (S.restrictCFamily V i).t y = x := by
  intro x
  have hx : x ∈ Set.range (V x).ι := by
    rw [Scheme.Opens.range_ι]
    exact hV x
  obtain ⟨y, hy⟩ := hx
  exact ⟨x, y, hy⟩

/-- The comparison of an inverse-image square is the published comparison of the
restricted square. -/
lemma restrictFamily_C (x : S.X) : (S.restrictFamily V x).C =
    PicardGroupoid.squareGluingComparison
      (leftRestriction S.i₁ S.j₁ (V x)) (rightRestriction S.i₁ S.i₂ S.j₁ S.j₂ S.w (V x))
      (S.j₁ ∣_ (V x)) (S.j₂ ∣_ (V x)) (restriction_comm S.i₁ S.i₂ S.j₁ S.j₂ S.w (V x)) :=
  rfl

/-- Restriction along an inclusion cube is the published restriction to an open. -/
lemma restrictCFamily_R (x : S.X) : (S.restrictCFamily V x).R =
    SquareGluingRestriction.toOpen S.i₁ S.i₂ S.j₁ S.j₂ S.w (V x) := rfl

lemma trivialFamily_eq (x : S.X) : S.trivialFamily V x =
    (Core.mk (LineBundle.trivial (V x).toScheme) : PicardGroupoid (V x).toScheme) := rfl

/-- The published effectivity predicate gives a realization of each restricted
datum by the trivial line bundle.

This is a theorem proved by rewriting along functor equalities, not a definition:
proofs abstracted from definition bodies, or beta-redexes in binder types, make the
kernel compare objects by unfolding actual pullbacks of modules. -/
theorem nonempty_trivialFamily {D : S.GD}
    (hE : ∀ x, InfinitesimalLocalEffectivity.IsEffectiveOn S.i₁ S.i₂ S.j₁ S.j₂ S.w D (V x))
    (x : S.X) :
    Nonempty ((S.restrictFamily V x).C.obj (S.trivialFamily V x) ≅
      (S.restrictCFamily V x).R.obj D) := by
  rw [restrictFamily_C, restrictCFamily_R, trivialFamily_eq]
  exact hE x

/-- Gluing data effective on an open neighborhood of every point are realized,
provided the comparison is full and faithful on cartesian open cubes. -/
theorem exists_iso_of_effective {D : S.GD} (hV : ∀ x, x ∈ V x) (hff : FFOnCart S)
    (hE : ∀ x, InfinitesimalLocalEffectivity.IsEffectiveOn S.i₁ S.i₂ S.j₁ S.j₂ S.w D (V x)) :
    ∃ L : PicardGroupoid S.X, Nonempty (S.C.obj L ≅ D) :=
  Cech.exists_iso (T := S.restrictFamily V) (N := S.trivialFamily V) (S.restrictCFamily V)
    (S.cart_restrictCFamily V) (S.restrictCFamily_cover V hV) hff
    (fun x ↦ (S.nonempty_trivialFamily V hE x).some)

end Family

end Sq

section Affine

variable {k R A B C : Type u} [Field k] [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k R] [Algebra k A] [Algebra k B] [Algebra k C]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (p : R →ₐ[k] A) (q : R →ₐ[k] B) (a : A →ₐ[k] C) (b : B →ₐ[k] C)
  (h : IsPullback (CommRingCat.ofHom p.toRingHom) (CommRingCat.ofHom q.toRingHom)
    (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom b.toRingHom))

/-- The actual base change of an affine ring square. -/
@[simps]
def affineSq : Sq.{u} where
  X₀ := (relativeSpace f).obj (affineBase k C)
  X₁ := (relativeSpace f).obj (affineBase k A)
  X₂ := (relativeSpace f).obj (affineBase k B)
  X := (relativeSpace f).obj (affineBase k R)
  i₁ := (relativeSpace f).map (affineBaseMap a)
  i₂ := (relativeSpace f).map (affineBaseMap b)
  j₁ := (relativeSpace f).map (affineBaseMap p)
  j₂ := (relativeSpace f).map (affineBaseMap q)
  w := PicardGroupoid.relativeSquare_comm f _ _ _ _ (PicardGroupoid.affineSquare_comm p q a b h)

/-- The comparison functor of the base-changed square is the published affine
comparison. -/
lemma affineSq_C :
    (affineSq f p q a b h).C = PicardGroupoid.affineSquareComparison f p q a b h := rfl

/-- Every cartesian open cube into the base-changed square has ring pullbacks of
global sections over all affine opens of its total scheme. -/
lemma affineRestrictedCubes {T : Sq.{u}} (c : CubeMap (affineSq f p q a b h) T) (hc : c.Cart)
    [IsOpenImmersion c.t] :
    SquareGluingFullyFaithful.AffineRestrictedCubes T.i₁ T.i₂ T.j₁ T.j₂ := by
  intro U hU
  have : IsAffine U.toScheme := hU
  have hc' := (T.cart_restrictC U).comp hc
  refine ⟨(T.i₁ ≫ T.j₁) ⁻¹ᵁ U, leftRestriction T.i₁ T.j₁ U,
    rightRestriction T.i₁ T.i₂ T.j₁ T.j₂ T.w U, ((T.i₁ ≫ T.j₁) ⁻¹ᵁ U).ι,
    leftRestriction_ι T.i₁ T.j₁ U, rightRestriction_ι T.i₁ T.i₂ T.j₁ T.j₂ T.w U, ?_⟩
  exact InfinitesimalCartesianCube.cartesianCube_appTop_isPullback f p q a b h
    (U.ι ≫ c.t) (T.j₁ ∣_ U) (T.j₂ ∣_ U) (leftRestriction T.i₁ T.j₁ U)
    (rightRestriction T.i₁ T.i₂ T.j₁ T.j₂ T.w U)
    ((T.j₁ ⁻¹ᵁ U).ι ≫ c.g₁) ((T.j₂ ⁻¹ᵁ U).ι ≫ c.g₂) (((T.i₁ ≫ T.j₁) ⁻¹ᵁ U).ι ≫ c.g₀)
    hc'.1 hc'.2.1 hc'.2.2 (comp (T.restrictC U) c).k₂ (T.restrict U).w

/-- The comparison is full and faithful on every cartesian open cube into the
base-changed square. -/
lemma ffOnCart : FFOnCart (affineSq f p q a b h) := by
  intro T c hc hct
  have hR := affineRestrictedCubes f p q a b h c hc
  have hcov : SquareGluingFullyFaithful.CommonAffineTrivializingCovers T.X :=
    fun L L' ↦ LineBundle.exists_commonAffineTrivializingCover L L'
  exact ⟨SquareGluingFullyFaithful.full _ _ _ _ T.w hR hcov,
    SquareGluingFullyFaithful.faithful _ _ _ _ T.w hR hcov⟩

/-- The identity cube of a square. -/
@[simps]
def idC (S : Sq.{u}) : CubeMap S S where
  t := 𝟙 _
  g₁ := 𝟙 _
  g₂ := 𝟙 _
  g₀ := 𝟙 _
  h₁ := by simp
  h₂ := by simp
  k₁ := by simp
  k₂ := by simp

lemma cart_idC (S : Sq.{u}) : (idC S).Cart :=
  ⟨IsPullback.of_id_fst, IsPullback.of_id_fst, IsPullback.of_id_fst⟩

/-- Every actual gluing datum on the base-changed square is realized by an actual
line bundle. -/
lemma essSurj (hb : Function.Surjective b) (hn : IsNilpotent (RingHom.ker b.toRingHom)) :
    (affineSq f p q a b h).C.EssSurj := by
  constructor
  intro D
  have E := fun x : (affineSq f p q a b h).X ↦
    InfinitesimalLocalEffectivity.affineSquareNeighborhood f p q a b h hb hn D ⊤ x
      (TopologicalSpace.Opens.mem_top x)
  exact (affineSq f p q a b h).exists_iso_of_effective (fun x ↦ (E x).opens)
    (fun x ↦ (E x).mem) (ffOnCart f p q a b h) (fun x ↦ (E x).effective)

/-- The published affine comparison is an equivalence. -/
theorem affineSquareComparison_isEquivalence (hb : Function.Surjective b)
    (hn : IsNilpotent (RingHom.ker b.toRingHom)) :
    (PicardGroupoid.affineSquareComparison f p q a b h).IsEquivalence := by
  have hS := ffOnCart f p q a b h _ (idC _) (cart_idC _)
    (inferInstanceAs (IsOpenImmersion (𝟙 _)))
  exact { faithful := hS.2, full := hS.1, essSurj := essSurj f p q a b h hb hn }

end Affine

end SquareGluingDescent

/-- Actual line bundles and their actual isomorphisms glue across affine ring
pullback squares with one surjective map having nilpotent kernel. -/
theorem fieldPicardInfinitesimalGluing : FieldPicardInfinitesimalGluingStatement.{u} := by
  intro k _ X f _ R A B C _ _ _ _ _ _ _ _ p q a b h hb hn
  exact SquareGluingDescent.affineSquareComparison_isEquivalence f p q a b h hb hn

end Langlands.AlgebraicGeometry.Picard
