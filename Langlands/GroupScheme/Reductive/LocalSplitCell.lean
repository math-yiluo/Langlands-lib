import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Rational.SteinbergRootProduct
import Langlands.GroupScheme.Torus.ExponentHomomorphisms

/-! # Root parametrizations and big-cell maps over a ring -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))}

/-- The additive group `𝔾ₐ` over `Spec R`. -/
abbrev Ga (R : Type u) [CommRing R] : GroupScheme (Spec (CommRingCat.of R)) :=
  VectorGroup.groupScheme (CommRingCat.of R) 1

/-- The value `u(c)` of a map from `𝔾ₐ` at a global function `c` of the test scheme. -/
def rootPoint (u : Ga R ⟶ G) (Z : Over (Spec (CommRingCat.of R))) (c : Γ(Z.left, ⊤)) :
    Z ⟶ G.X :=
  VectorGroup.scalarPoint (CommRingCat.of R) Z c ≫ u.hom.hom

theorem comp_rootPoint (u : Ga R ⟶ G) {Z W : Over (Spec (CommRingCat.of R))} (f : W ⟶ Z)
    (c : Γ(Z.left, ⊤)) : f ≫ rootPoint u Z c = rootPoint u W (f.left.appTop c) := by
  rw [rootPoint, ← Category.assoc, VectorGroup.scalarPoint_comp, rootPoint]

/-- `u : 𝔾ₐ ⟶ G` parametrizes the root group of the exponent character `m` of the split
torus `i`: it is a closed immersion onto the whole relative root subgroup, and the torus
acts on it through `m`. -/
structure IsRootParametrization (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (m : I → ℤ) (u : Ga R ⟶ G) : Prop where
  represents : (RelativeRoot.subgroup (S := splitTorus.commGroupScheme _ I) i
    (splitTorus.exponentCharacter _ I m)).IsRepresentedBy u
  isClosedSubgroup : IsClosedSubgroup u
  equivariant : ∀ (Z : Over (Spec (CommRingCat.of R)))
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (c : Γ(Z.left, ⊤)),
    (t ≫ i.hom.hom) * rootPoint u Z c * (t ≫ i.hom.hom)⁻¹ =
      rootPoint u Z (VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
        (splitTorus.exponentCharacter _ I m) Z t * c)

/-- The point `u'(-1) u(1) u'(-1)` of `G` over the base. For opposite root
parametrizations `u, u'` with the standard normalization it represents the simple
reflection of the root of `u`. -/
def weylPoint (u u' : Ga R ⟶ G) : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X :=
  rootPoint u' _ (-1) * rootPoint u _ 1 * rootPoint u' _ (-1)

/-- A point `n` of `G` over the base normalizes the split torus `i`, acting on it by the
torus automorphism with exponent map `f`: `n t n⁻¹ = f(t)` on every test. -/
def IsWeylPoint [DecidableEq I] (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (n : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X) (f : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)) : Prop :=
  ∀ (Z : Over (Spec (CommRingCat.of R)))
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X),
    (toUnit Z ≫ n) * (t ≫ i.hom.hom) * (toUnit Z ≫ n)⁻¹ =
      t ≫ (splitTorus.exponentIso _ I f).hom.hom.hom ≫ i.hom.hom

/-! ### The big-cell map -/

/-- The source `𝔾ₐᵐ × T × 𝔾ₐⁿ` of a big-cell map. -/
abbrev cellObj (R : Type u) [CommRing R] (I : Type u) [Fintype I] (m n : ℕ) :
    Over (Spec (CommRingCat.of R)) :=
  ((VectorGroup.groupScheme (CommRingCat.of R) m).X ⊗
    (splitTorus (Spec (CommRingCat.of R)) I).X) ⊗ (VectorGroup.groupScheme (CommRingCat.of R) n).X

variable {J : Type u}

/-- The ordered product `∏ₖ u_{e k}(c k)`, factors taken in increasing order of `k`. -/
def orderedProduct (u : J → (Ga R ⟶ G)) {r : ℕ} (e : Fin r → J)
    (Z : Over (Spec (CommRingCat.of R))) (c : Fin r → Γ(Z.left, ⊤)) : Z ⟶ G.X :=
  (List.ofFn fun k => rootPoint (u (e k)) Z (c k)).prod

omit [Fintype I] in
private theorem comp_list_prod {Z W : Over (Spec (CommRingCat.of R))} (f : W ⟶ Z)
    (l : List (Z ⟶ G.X)) : f ≫ l.prod = (l.map (fun g => f ≫ g)).prod := by
  induction l with
  | nil => simp
  | cons g l ih => simp only [List.prod_cons, List.map_cons, MonObj.comp_mul, ih]

theorem comp_orderedProduct (u : J → (Ga R ⟶ G)) {r : ℕ} (e : Fin r → J)
    {Z W : Over (Spec (CommRingCat.of R))} (f : W ⟶ Z) (c : Fin r → Γ(Z.left, ⊤)) :
    f ≫ orderedProduct u e Z c = orderedProduct u e W (fun k => f.left.appTop (c k)) := by
  simp only [orderedProduct, comp_list_prod, List.map_ofFn, Function.comp_def, comp_rootPoint]

/-- The big-cell formula on points: `(∏ₖ u_{neg k}(v k)) · i(t) · (∏ₖ u_{pos k}(w k))`. -/
def cellPoint (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (u : J → (Ga R ⟶ G))
    {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J) (Z : Over (Spec (CommRingCat.of R)))
    (v : Fin m → Γ(Z.left, ⊤)) (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X)
    (w : Fin n → Γ(Z.left, ⊤)) : Z ⟶ G.X :=
  orderedProduct u neg Z v * (t ≫ i.hom.hom) * orderedProduct u pos Z w

theorem comp_cellPoint (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (u : J → (Ga R ⟶ G))
    {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J) {Z W : Over (Spec (CommRingCat.of R))}
    (f : W ⟶ Z) (v : Fin m → Γ(Z.left, ⊤)) (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X)
    (w : Fin n → Γ(Z.left, ⊤)) :
    f ≫ cellPoint i u neg pos Z v t w =
      cellPoint i u neg pos W (fun k => f.left.appTop (v k)) (f ≫ t)
        (fun k => f.left.appTop (w k)) := by
  simp only [cellPoint, MonObj.comp_mul, comp_orderedProduct, Category.assoc]

/-- The three components of a point of the cell source. -/
def negCoord {m n : ℕ} {Z : Over (Spec (CommRingCat.of R))} (x : Z ⟶ cellObj R I m n) :
    Fin m → Γ(Z.left, ⊤) :=
  (VectorGroup.coordinates (CommRingCat.of R) m Z (x ≫ fst _ _ ≫ fst _ _)).toAdd

/-- The torus component of a point of the cell source. -/
def torusCoord {m n : ℕ} {Z : Over (Spec (CommRingCat.of R))} (x : Z ⟶ cellObj R I m n) :
    Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X :=
  x ≫ fst _ _ ≫ snd _ _

/-- The positive-root coordinates of a point of the cell source. -/
def posCoord {m n : ℕ} {Z : Over (Spec (CommRingCat.of R))} (x : Z ⟶ cellObj R I m n) :
    Fin n → Γ(Z.left, ⊤) :=
  (VectorGroup.coordinates (CommRingCat.of R) n Z (x ≫ snd _ _)).toAdd

/-- The big-cell map `𝔾ₐᵐ × T × 𝔾ₐⁿ ⟶ G`, `(v, t, w) ↦ (∏ₖ u_{neg k}(vₖ)) i(t) (∏ₖ u_{pos k}(wₖ))`. -/
def cellMap (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (u : J → (Ga R ⟶ G))
    {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J) : cellObj R I m n ⟶ G.X :=
  cellPoint i u neg pos _ (negCoord (𝟙 _)) (torusCoord (𝟙 _)) (posCoord (𝟙 _))

theorem negCoord_comp {m n : ℕ} {Z W : Over (Spec (CommRingCat.of R))} (f : W ⟶ Z)
    (x : Z ⟶ cellObj R I m n) :
    negCoord (f ≫ x) = fun k => f.left.appTop (negCoord x k) := by
  simp only [negCoord, Category.assoc, VectorGroup.coordinates_comp]

theorem posCoord_comp {m n : ℕ} {Z W : Over (Spec (CommRingCat.of R))} (f : W ⟶ Z)
    (x : Z ⟶ cellObj R I m n) :
    posCoord (f ≫ x) = fun k => f.left.appTop (posCoord x k) := by
  simp only [posCoord, Category.assoc, VectorGroup.coordinates_comp]

theorem torusCoord_comp {m n : ℕ} {Z W : Over (Spec (CommRingCat.of R))} (f : W ⟶ Z)
    (x : Z ⟶ cellObj R I m n) : torusCoord (f ≫ x) = f ≫ torusCoord x := by
  simp only [torusCoord, Category.assoc]

/-- On points, the big-cell map is given by the big-cell formula. -/
theorem comp_cellMap (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (u : J → (Ga R ⟶ G))
    {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J) {Z : Over (Spec (CommRingCat.of R))}
    (x : Z ⟶ cellObj R I m n) :
    x ≫ cellMap i u neg pos = cellPoint i u neg pos Z (negCoord x) (torusCoord x) (posCoord x) := by
  rw [cellMap, comp_cellPoint]
  have h := (Category.comp_id x).symm
  conv_rhs => rw [h, negCoord_comp, posCoord_comp, torusCoord_comp]

end Langlands.GroupScheme.LocalSplitCell

namespace Langlands.GroupScheme

open LocalSplitCell

/-- **Root groups over a reduced local ring.** Let `G` be a reductive group over a reduced
local ring `R` with a closed coordinate split torus `i`, maximal on every residue-field fibre,
and a fibrewise root datum `P`. For every base `b` of `P` there is a family of root
parametrizations `u α : 𝔾ₐ ⟶ G`, one for each root, such that for each simple root `a` the
point `u_{-a}(-1) u_a(1) u_{-a}(-1)` normalizes the torus and acts on it by the simple
reflection `s_a` (Conrad, *Reductive group schemes*, Thm. 4.1.4 and Cor. 5.1.9). -/
def LocalSplitRootGroupStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsReduced R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom],
    IsReductive G →
    ∀ (I : Type u) [Fintype I] [DecidableEq I] (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
      IsClosedSubgroup i →
      (∀ s : Spec (CommRingCat.of R),
        IsMaximalTorus
          (T := (CommGroupScheme.baseChange
            ((Spec (CommRingCat.of R)).fromSpecResidueField s)).obj
              (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I))
          ((GroupScheme.baseChange
            ((Spec (CommRingCat.of R)).fromSpecResidueField s)).map i)) →
      ∀ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)), IsFibrewiseRootDatumOf I G i P →
      ∀ b : P.Base, ∃ u : J → (Ga R ⟶ G),
        (∀ α, IsRootParametrization i (P.root α) (u α)) ∧
        ∀ a ∈ b.support,
          IsWeylPoint i (weylPoint (u a) (u (P.reflectionPerm a a))) (P.reflection a)

/-- **The big cell over a reduced local ring.** In the setting of
`LocalSplitRootGroupStatement`, for every base `b`, every family of root parametrizations
and all enumerations of the negative and the positive roots, the big-cell map
`𝔾ₐᵐ × T × 𝔾ₐⁿ ⟶ G`, `(v, t, w) ↦ (∏ₖ u_{neg k}(vₖ)) i(t) (∏ₖ u_{pos k}(wₖ))`, is an open
immersion (Conrad, *Reductive group schemes*, Thm. 5.1.13). -/
def LocalSplitBigCellStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsReduced R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom],
    IsReductive G →
    ∀ (I : Type u) [Fintype I] (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
      IsClosedSubgroup i →
      (∀ s : Spec (CommRingCat.of R),
        IsMaximalTorus
          (T := (CommGroupScheme.baseChange
            ((Spec (CommRingCat.of R)).fromSpecResidueField s)).obj
              (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I))
          ((GroupScheme.baseChange
            ((Spec (CommRingCat.of R)).fromSpecResidueField s)).map i)) →
      ∀ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)), IsFibrewiseRootDatumOf I G i P →
      ∀ (b : P.Base) (u : J → (Ga R ⟶ G)), (∀ α, IsRootParametrization i (P.root α) (u α)) →
      ∀ (m n : ℕ) (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α}),
        IsOpenImmersion (cellMap i u (fun k => (neg k : J)) (fun k => (pos k : J))).left

end Langlands.GroupScheme
