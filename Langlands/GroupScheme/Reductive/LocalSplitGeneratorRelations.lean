import Langlands.GroupScheme.Reductive.LocalSplitClosedResidueCellIsomorphism

/-! # Big-cell gluing from right translation by torus and root points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj nonZeroDivisors

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace GenericLine

open Polynomial

variable (B : Type u) [CommRing B] [IsLocalRing B]

/-- Polynomials whose reduction modulo the maximal ideal vanishes: the generic point of the
closed fibre of the affine line over `B`. -/
def genericIdeal : Ideal B[X] := RingHom.ker (Polynomial.mapRingHom (IsLocalRing.residue B))

instance : (genericIdeal B).IsPrime := RingHom.ker_isPrime _

/-- The closed point `X = a` of the affine line over the closed point of `B`. -/
def pointIdeal (a : B) : Ideal B[X] :=
  (IsLocalRing.maximalIdeal B).comap (Polynomial.evalRingHom a)

instance (a : B) : (pointIdeal B a).IsPrime := Ideal.IsPrime.comap _

/-- The local ring of the line at the generic point of its closed fibre. -/
abbrev Generic : Type u := Localization.AtPrime (genericIdeal B)

/-- The local ring of the line at the point `X = a` of its closed fibre. -/
abbrev AtPoint (a : B) : Type u := Localization.AtPrime (pointIdeal B a)

variable {B}

theorem mem_genericIdeal_iff (f : B[X]) :
    f ∈ genericIdeal B ↔ f.map (IsLocalRing.residue B) = 0 :=
  RingHom.mem_ker

theorem genericIdeal_le_pointIdeal (a : B) : genericIdeal B ≤ pointIdeal B a := by
  intro f hf
  rw [mem_genericIdeal_iff] at hf
  change Polynomial.eval a f ∈ IsLocalRing.maximalIdeal B
  rw [← IsLocalRing.residue_eq_zero_iff, ← Polynomial.eval_map_apply, hf, Polynomial.eval_zero]

/-- A polynomial with a coefficient outside the maximal ideal is a non-zero-divisor. -/
theorem mem_nonZeroDivisors_of_notMem_genericIdeal {f : B[X]} (hf : f ∉ genericIdeal B) :
    f ∈ B[X]⁰ := by
  rw [mem_genericIdeal_iff] at hf
  obtain ⟨n, hn⟩ : ∃ n, (f.map (IsLocalRing.residue B)).coeff n ≠ 0 := by
    by_contra h
    exact hf (Polynomial.ext fun n => by
      rw [Polynomial.coeff_zero]
      by_contra hn
      exact h ⟨n, hn⟩)
  rw [Polynomial.coeff_map] at hn
  have hu : IsUnit (f.coeff n) := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff]
    exact hn
  exact Polynomial.mem_nonzeroDivisors_of_coeff_mem n hu.mem_nonZeroDivisors

theorem notMem_pointIdeal_iff (a : B) (f : B[X]) :
    f ∉ pointIdeal B a ↔ IsUnit (Polynomial.eval a f) :=
  IsLocalRing.notMem_maximalIdeal

/-- Generization from the point `X = a` to the generic point of the closed fibre. -/
def toGeneric (a : B) : AtPoint B a →+* Generic B :=
  IsLocalization.lift (M := (pointIdeal B a).primeCompl) (S := AtPoint B a)
    (g := algebraMap B[X] (Generic B)) fun y =>
      IsLocalization.map_units (Generic B)
        (⟨y.1, fun h => y.2 (genericIdeal_le_pointIdeal a h)⟩ : (genericIdeal B).primeCompl)

theorem toGeneric_algebraMap (a : B) (f : B[X]) :
    toGeneric a (algebraMap B[X] (AtPoint B a) f) = algebraMap B[X] (Generic B) f :=
  IsLocalization.lift_eq _ f

theorem toGeneric_comp (a : B) :
    (toGeneric a).comp (algebraMap B[X] (AtPoint B a)) = algebraMap B[X] (Generic B) :=
  RingHom.ext (toGeneric_algebraMap a)

/-- Generization is injective: no nonzero polynomial is killed by a polynomial with a unit
coefficient. -/
theorem toGeneric_injective (a : B) : Function.Injective (toGeneric a) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨f, s, rfl⟩ := IsLocalization.exists_mk'_eq (pointIdeal B a).primeCompl z
  have hz' : algebraMap B[X] (Generic B) f = 0 := by
    rw [toGeneric, IsLocalization.lift_mk'] at hz
    have hu := IsLocalization.map_units (Generic B)
      (⟨s.1, fun h => s.2 (genericIdeal_le_pointIdeal a h)⟩ : (genericIdeal B).primeCompl)
    simpa using hz
  obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff (genericIdeal B).primeCompl _ f).mp hz'
  have hf : f = 0 :=
    (mul_left_mem_nonZeroDivisors_eq_zero_iff
      (mem_nonZeroDivisors_of_notMem_genericIdeal c.2)).mp hc
  rw [hf, IsLocalization.mk'_zero]

/-- Evaluation at `X = a`. -/
def evalAt (a : B) : AtPoint B a →+* B :=
  IsLocalization.lift (M := (pointIdeal B a).primeCompl) (S := AtPoint B a)
    (g := Polynomial.evalRingHom a) fun y => (notMem_pointIdeal_iff a y.1).mp y.2

theorem evalAt_algebraMap (a : B) (f : B[X]) :
    evalAt a (algebraMap B[X] (AtPoint B a) f) = Polynomial.eval a f :=
  IsLocalization.lift_eq _ f

theorem evalAt_comp_C (a : B) :
    ((evalAt a).comp (algebraMap B[X] (AtPoint B a))).comp Polynomial.C = RingHom.id B := by
  ext b
  simp [evalAt_algebraMap]

theorem evalAt_surjective (a : B) : Function.Surjective (evalAt a) := fun b =>
  ⟨algebraMap B[X] (AtPoint B a) (Polynomial.C b), by
    rw [evalAt_algebraMap, Polynomial.eval_C]⟩

instance (a : B) : IsLocalHom (evalAt a) :=
  IsLocalHom.of_surjective _ (evalAt_surjective a)

theorem evalAt_comp (a : B) :
    (evalAt a).comp (algebraMap B[X] (AtPoint B a)) = Polynomial.evalRingHom a :=
  RingHom.ext (evalAt_algebraMap a)

omit [IsLocalRing B] in
theorem evalRingHom_comp_C (a : B) : (Polynomial.evalRingHom a).comp Polynomial.C = RingHom.id B :=
  RingHom.ext fun _ => Polynomial.eval_C

/-- The affine interpolation `a (1 - X) + b X` from `a` at `X = 0` to `b` at `X = 1`. -/
def lineCoeff (a b : B) : B[X] := Polynomial.C a * (1 - Polynomial.X) + Polynomial.C b * Polynomial.X

omit [IsLocalRing B] in
@[simp] theorem eval_zero_lineCoeff (a b : B) : (lineCoeff a b).eval 0 = a := by
  simp [lineCoeff]

omit [IsLocalRing B] in
@[simp] theorem eval_one_lineCoeff (a b : B) : (lineCoeff a b).eval 1 = b := by
  simp [lineCoeff]

theorem lineCoeff_notMem_pointIdeal_zero {a : B} (ha : IsUnit a) (b : B) :
    lineCoeff a b ∉ pointIdeal B 0 := by
  rw [notMem_pointIdeal_iff, eval_zero_lineCoeff]
  exact ha

theorem lineCoeff_notMem_pointIdeal_one (a : B) {b : B} (hb : IsUnit b) :
    lineCoeff a b ∉ pointIdeal B 1 := by
  rw [notMem_pointIdeal_iff, eval_one_lineCoeff]
  exact hb

theorem lineCoeff_notMem_genericIdeal {a : B} (ha : IsUnit a) (b : B) :
    lineCoeff a b ∉ genericIdeal B := fun h =>
  lineCoeff_notMem_pointIdeal_zero ha b (genericIdeal_le_pointIdeal 0 h)

end GenericLine

namespace LocalSplitCell

section CellCoordinates

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {m n : ℕ}

/-- The point of the coordinate cell with prescribed negative, torus and positive
coordinates. -/
def mkCellPoint (Z : Over (Spec (CommRingCat.of R))) (v : Fin m → Γ(Z.left, ⊤))
    (t : I → (Γ(Z.left, ⊤))ˣ) (w : Fin n → Γ(Z.left, ⊤)) : Z ⟶ cellObj R I m n :=
  (Equiv.ofBijective _ (LocalSplitBigCell.coordTriple_bijective R I m n Z)).symm
    (v, (splitTorus.pointsEquiv I Z).symm t, w)

theorem coordTriple_mkCellPoint (Z : Over (Spec (CommRingCat.of R))) (v : Fin m → Γ(Z.left, ⊤))
    (t : I → (Γ(Z.left, ⊤))ˣ) (w : Fin n → Γ(Z.left, ⊤)) :
    LocalSplitBigCell.coordTriple (mkCellPoint Z v t w) =
      (v, (splitTorus.pointsEquiv I Z).symm t, w) :=
  (Equiv.ofBijective _ (LocalSplitBigCell.coordTriple_bijective R I m n Z)).apply_symm_apply _

theorem negCoord_mkCellPoint (Z : Over (Spec (CommRingCat.of R))) (v : Fin m → Γ(Z.left, ⊤))
    (t : I → (Γ(Z.left, ⊤))ˣ) (w : Fin n → Γ(Z.left, ⊤)) :
    negCoord (mkCellPoint Z v t w) = v :=
  congrArg Prod.fst (coordTriple_mkCellPoint Z v t w)

theorem torusCoord_mkCellPoint (Z : Over (Spec (CommRingCat.of R))) (v : Fin m → Γ(Z.left, ⊤))
    (t : I → (Γ(Z.left, ⊤))ˣ) (w : Fin n → Γ(Z.left, ⊤)) :
    splitTorus.pointsEquiv I Z (torusCoord (mkCellPoint Z v t w)) = t := by
  have h := congrArg (fun q => q.2.1) (coordTriple_mkCellPoint Z v t w)
  simp only [LocalSplitBigCell.coordTriple] at h
  rw [h, MulEquiv.apply_symm_apply]

theorem posCoord_mkCellPoint (Z : Over (Spec (CommRingCat.of R))) (v : Fin m → Γ(Z.left, ⊤))
    (t : I → (Γ(Z.left, ⊤))ˣ) (w : Fin n → Γ(Z.left, ⊤)) :
    posCoord (mkCellPoint Z v t w) = w :=
  congrArg (fun q => q.2.2) (coordTriple_mkCellPoint Z v t w)

/-- Points of the coordinate cell are determined by their coordinates. -/
theorem cellPoint_ext {Z : Over (Spec (CommRingCat.of R))} {x y : Z ⟶ cellObj R I m n}
    (hv : negCoord x = negCoord y)
    (ht : splitTorus.pointsEquiv I Z (torusCoord x) = splitTorus.pointsEquiv I Z (torusCoord y))
    (hw : posCoord x = posCoord y) : x = y :=
  (LocalSplitBigCell.coordTriple_bijective R I m n Z).1
    (Prod.ext hv (Prod.ext ((splitTorus.pointsEquiv I Z).injective ht) hw))

theorem comp_mkCellPoint {Z W : Over (Spec (CommRingCat.of R))} (k : W ⟶ Z)
    (v : Fin m → Γ(Z.left, ⊤)) (t : I → (Γ(Z.left, ⊤))ˣ) (w : Fin n → Γ(Z.left, ⊤)) :
    k ≫ mkCellPoint Z v t w =
      mkCellPoint W (fun a => k.left.appTop (v a)) (splitTorus.unitsRestrict I k t)
        (fun a => k.left.appTop (w a)) := by
  apply cellPoint_ext
  · rw [negCoord_comp, negCoord_mkCellPoint, negCoord_mkCellPoint]
  · rw [torusCoord_comp, splitTorus.pointsEquiv_naturality, torusCoord_mkCellPoint,
      torusCoord_mkCellPoint]
  · rw [posCoord_comp, posCoord_mkCellPoint, posCoord_mkCellPoint]

/-- Restriction along `Spec` of a ring map, read through the global-section isomorphisms. -/
theorem specMap_appTop_ΓSpecIso_inv {L L' : Type u} [CommRing L] [CommRing L'] (κ : L →+* L')
    (a : L) :
    (Spec.map (CommRingCat.ofHom κ)).appTop ((Scheme.ΓSpecIso (CommRingCat.of L)).inv a) =
      (Scheme.ΓSpecIso (CommRingCat.of L')).inv (κ a) := by
  have h := congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom κ))
  exact h.symm

/-- The point of the coordinate cell over `Spec L` with coordinates in `L`. -/
def specCellPoint (L : Type u) [CommRing L] (sL : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R))
    (a : Fin m → L) (τ : I → Lˣ) (b : Fin n → L) : Over.mk sL ⟶ cellObj R I m n :=
  mkCellPoint (Over.mk sL) (fun k => (Scheme.ΓSpecIso (CommRingCat.of L)).inv (a k))
    (fun j => Units.map (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom.toMonoidHom (τ j))
    (fun k => (Scheme.ΓSpecIso (CommRingCat.of L)).inv (b k))

theorem comp_specCellPoint {L L' : Type u} [CommRing L] [CommRing L'] (κ : L →+* L')
    {sL : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R)}
    {sL' : Spec (CommRingCat.of L') ⟶ Spec (CommRingCat.of R)} (k : Over.mk sL' ⟶ Over.mk sL)
    (hk : k.left = Spec.map (CommRingCat.ofHom κ)) (a : Fin m → L) (τ : I → Lˣ) (b : Fin n → L) :
    k ≫ specCellPoint L sL a τ b =
      specCellPoint L' sL' (fun k => κ (a k)) (fun j => Units.map κ.toMonoidHom (τ j))
        (fun k => κ (b k)) := by
  rw [specCellPoint, comp_mkCellPoint, specCellPoint]
  congr 1
  · funext c
    rw [hk]
    exact specMap_appTop_ΓSpecIso_inv κ (a c)
  · funext j
    apply Units.ext
    change k.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of L)).inv (τ j : L)) =
      (Scheme.ΓSpecIso (CommRingCat.of L')).inv (κ (τ j : L))
    rw [hk]
    exact specMap_appTop_ΓSpecIso_inv κ _
  · funext c
    rw [hk]
    exact specMap_appTop_ΓSpecIso_inv κ (b c)

/-- Coordinates in `B` of a point of the cell over `Spec B`. -/
def negVal {B : Type u} [CommRing B] {sB : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)}
    (x : Over.mk sB ⟶ cellObj R I m n) (k : Fin m) : B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom (negCoord x k)

/-- Positive coordinates in `B` of a point of the cell over `Spec B`. -/
def posVal {B : Type u} [CommRing B] {sB : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)}
    (x : Over.mk sB ⟶ cellObj R I m n) (k : Fin n) : B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom (posCoord x k)

/-- Torus coordinates in `Bˣ` of a point of the cell over `Spec B`. -/
def torusVal {B : Type u} [CommRing B] {sB : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)}
    (x : Over.mk sB ⟶ cellObj R I m n) (j : I) : Bˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.toMonoidHom
    (splitTorus.pointsEquiv I _ (torusCoord x) j)

theorem eq_specCellPoint {B : Type u} [CommRing B]
    {sB : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)} (x : Over.mk sB ⟶ cellObj R I m n) :
    specCellPoint B sB (negVal x) (torusVal x) (posVal x) = x := by
  apply cellPoint_ext
  · rw [specCellPoint, negCoord_mkCellPoint]
    funext k
    exact (Scheme.ΓSpecIso (CommRingCat.of B)).hom_inv_id_apply _
  · rw [specCellPoint, torusCoord_mkCellPoint]
    funext j
    apply Units.ext
    exact (Scheme.ΓSpecIso (CommRingCat.of B)).hom_inv_id_apply _
  · rw [specCellPoint, posCoord_mkCellPoint]
    funext k
    exact (Scheme.ΓSpecIso (CommRingCat.of B)).hom_inv_id_apply _

end CellCoordinates

section LineData

open Polynomial GenericLine

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {m n : ℕ}

/-- The map of test objects induced by a ring map. -/
def specHom {L L' : Type u} [CommRing L] [CommRing L'] (κ : L →+* L')
    {sL : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R)}
    {sL' : Spec (CommRingCat.of L') ⟶ Spec (CommRingCat.of R)}
    (h : Spec.map (CommRingCat.ofHom κ) ≫ sL = sL') : Over.mk sL' ⟶ Over.mk sL :=
  Over.homMk (Spec.map (CommRingCat.ofHom κ)) h

theorem specHom_left {L L' : Type u} [CommRing L] [CommRing L'] (κ : L →+* L')
    {sL : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R)}
    {sL' : Spec (CommRingCat.of L') ⟶ Spec (CommRingCat.of R)}
    (h : Spec.map (CommRingCat.ofHom κ) ≫ sL = sL') :
    (specHom κ h).left = Spec.map (CommRingCat.ofHom κ) := rfl

theorem specMap_comp_specMap {L L' L'' : Type u} [CommRing L] [CommRing L'] [CommRing L'']
    (κ : L' →+* L'') (φ : L →+* L') (s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R)) :
    Spec.map (CommRingCat.ofHom κ) ≫ Spec.map (CommRingCat.ofHom φ) ≫ s =
      Spec.map (CommRingCat.ofHom (κ.comp φ)) ≫ s := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem specHom_comp {L L' L'' : Type u} [CommRing L] [CommRing L'] [CommRing L'']
    (κ : L →+* L') (κ' : L' →+* L'')
    {sL : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R)}
    {sL' : Spec (CommRingCat.of L') ⟶ Spec (CommRingCat.of R)}
    {sL'' : Spec (CommRingCat.of L'') ⟶ Spec (CommRingCat.of R)}
    (h : Spec.map (CommRingCat.ofHom κ) ≫ sL = sL')
    (h' : Spec.map (CommRingCat.ofHom κ') ≫ sL' = sL'')
    (h'' : Spec.map (CommRingCat.ofHom (κ'.comp κ)) ≫ sL = sL'') :
    specHom κ' h' ≫ specHom κ h = specHom (κ'.comp κ) h'' := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, specHom_left, specHom_left, specHom_left, CommRingCat.ofHom_comp,
    Spec.map_comp]

theorem specHom_congr {L L' : Type u} [CommRing L] [CommRing L'] {κ κ' : L →+* L'}
    (hκ : κ = κ') {sL : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R)}
    {sL' : Spec (CommRingCat.of L') ⟶ Spec (CommRingCat.of R)}
    (h : Spec.map (CommRingCat.ofHom κ) ≫ sL = sL')
    (h' : Spec.map (CommRingCat.ofHom κ') ≫ sL = sL') :
    specHom κ h = specHom κ' h' := by
  subst hκ
  rfl

theorem specHom_id {L : Type u} [CommRing L]
    {sL : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R)}
    (h : Spec.map (CommRingCat.ofHom (RingHom.id L)) ≫ sL = sL) :
    specHom (RingHom.id L) h = 𝟙 _ := by
  apply Over.OverMorphism.ext
  rw [specHom_left, Over.id_left, CommRingCat.ofHom_id, Spec.map_id]
  rfl

theorem specHom_comp_eq {L L' L'' : Type u} [CommRing L] [CommRing L'] [CommRing L'']
    {κ : L →+* L'} {κ' : L' →+* L''} {κ'' : L →+* L''} (hκ : κ'.comp κ = κ'')
    {sL : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R)}
    {sL' : Spec (CommRingCat.of L') ⟶ Spec (CommRingCat.of R)}
    {sL'' : Spec (CommRingCat.of L'') ⟶ Spec (CommRingCat.of R)}
    (h : Spec.map (CommRingCat.ofHom κ) ≫ sL = sL')
    (h' : Spec.map (CommRingCat.ofHom κ') ≫ sL' = sL'') :
    specHom κ' h' ≫ specHom κ h =
      specHom κ'' (by rw [← hκ, ← specMap_comp_specMap, h, h']) := by
  subst hκ
  exact specHom_comp κ κ' h h' _

/-- Evaluation at `X = a` is a section of the structure map of the local ring of the line
at `X = a`. -/
theorem specMap_evalAt_comp {B : Type u} [CommRing B] [IsLocalRing B] (a : B)
    (sB : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) :
    Spec.map (CommRingCat.ofHom (evalAt a)) ≫
        Spec.map (CommRingCat.ofHom ((algebraMap B[X] (AtPoint B a)).comp Polynomial.C)) ≫ sB =
      sB := by
  rw [specMap_comp_specMap, ← RingHom.comp_assoc, evalAt_comp_C, CommRingCat.ofHom_id,
    Spec.map_id, Category.id_comp]

variable {B : Type u} [CommRing B] (V : Fin m → B[X]) (T : I → B[X]) (W : Fin n → B[X])

/-- The cell point over `Spec L` whose coordinates are the images of the polynomials
`V`, `T`, `W` under `ψ`. -/
def linePoint {L : Type u} [CommRing L] (ψ : B[X] →+* L) (hu : ∀ j, IsUnit (ψ (T j)))
    (sL : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R)) :
    Over.mk sL ⟶ cellObj R I m n :=
  specCellPoint L sL (fun k => ψ (V k)) (fun j => (hu j).unit) (fun k => ψ (W k))

theorem specHom_comp_linePoint {L L' : Type u} [CommRing L] [CommRing L'] (κ : L →+* L')
    {ψ : B[X] →+* L} {ψ' : B[X] →+* L'} (hψ : κ.comp ψ = ψ') (hu : ∀ j, IsUnit (ψ (T j)))
    (hu' : ∀ j, IsUnit (ψ' (T j)))
    {sL : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R)}
    {sL' : Spec (CommRingCat.of L') ⟶ Spec (CommRingCat.of R)}
    (h : Spec.map (CommRingCat.ofHom κ) ≫ sL = sL') :
    specHom κ h ≫ linePoint V T W ψ hu sL = linePoint V T W ψ' hu' sL' := by
  subst hψ
  rw [linePoint, comp_specCellPoint κ _ (specHom_left κ h), linePoint]
  congr 1
  funext j
  apply Units.ext
  rfl

theorem linePoint_eq {L : Type u} [CommRing L] (ψ : B[X] →+* L) (hu : ∀ j, IsUnit (ψ (T j)))
    (sL : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R)) (a : Fin m → L) (τ : I → Lˣ)
    (b : Fin n → L) (ha : ∀ k, ψ (V k) = a k) (hτ : ∀ j, ψ (T j) = τ j)
    (hb : ∀ k, ψ (W k) = b k) :
    linePoint V T W ψ hu sL = specCellPoint L sL a τ b := by
  rw [linePoint]
  congr 1
  · exact funext ha
  · funext j
    exact Units.ext (hτ j)
  · exact funext hb

end LineData

section RightGood

open Polynomial GenericLine

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {m n : ℕ}
  {G H : GroupScheme (Spec (CommRingCat.of R))}

/-- `g` and `h` transfer right multiplication relations between cell points: whenever, over a
local test ring with separably closed residue field, the `G`-cell point of `x` times the
pullback of `g` is the `G`-cell point of `y`, the same holds in `H` with `h`. -/
def RightGood (Ω : cellObj R I m n ⟶ G.X) (Ω' : cellObj R I m n ⟶ H.X)
    {Z : Over (Spec (CommRingCat.of R))} (g : Z ⟶ G.X) (h : Z ⟶ H.X) : Prop :=
  ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsSepClosed (IsLocalRing.ResidueField B)]
    (sB : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (f : Over.mk sB ⟶ Z)
    (x y : Over.mk sB ⟶ cellObj R I m n),
    (x ≫ Ω) * (f ≫ g) = y ≫ Ω → (x ≫ Ω') * (f ≫ h) = y ≫ Ω'

/-- Every point over a local test ring with separably closed residue field is carried into
the cell by left multiplication with a cell point. -/
def HasCellFactors (Ω : cellObj R I m n ⟶ G.X) : Prop :=
  ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsSepClosed (IsLocalRing.ResidueField B)]
    (sB : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (g : Over.mk sB ⟶ G.X),
    ∃ p q : Over.mk sB ⟶ cellObj R I m n, (p ≫ Ω) * g = q ≫ Ω

variable {Ω : cellObj R I m n ⟶ G.X} {Ω' : cellObj R I m n ⟶ H.X}

theorem RightGood.comp {Z Z' : Over (Spec (CommRingCat.of R))} {g : Z ⟶ G.X} {h : Z ⟶ H.X}
    (hg : RightGood Ω Ω' g h) (k : Z' ⟶ Z) : RightGood Ω Ω' (k ≫ g) (k ≫ h) := by
  intro B _ _ _ sB f x y hxy
  rw [← Category.assoc] at hxy ⊢
  exact hg B sB (f ≫ k) x y hxy

theorem rightGood_one [Mono Ω] {Z : Over (Spec (CommRingCat.of R))} :
    RightGood Ω Ω' (1 : Z ⟶ G.X) (1 : Z ⟶ H.X) := by
  intro B _ _ _ sB f x y hxy
  rw [MonObj.comp_one, mul_one] at hxy ⊢
  rw [(cancel_mono Ω).mp hxy]

theorem RightGood.inv {Z : Over (Spec (CommRingCat.of R))} {g : Z ⟶ G.X} {h : Z ⟶ H.X}
    (hg : RightGood Ω Ω' g h) : RightGood Ω Ω' g⁻¹ h⁻¹ := by
  intro B _ _ _ sB f x y hxy
  rw [GrpObj.comp_inv, mul_inv_eq_iff_eq_mul] at hxy ⊢
  exact (hg B sB f y x hxy.symm).symm

/-- Over a local test ring with separably closed residue field, a right-good partner is
unique. -/
theorem RightGood.unique (hΩ : HasCellFactors Ω) {A : Type u} [CommRing A] [IsLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    {s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)} {g : Over.mk s ⟶ G.X}
    {h h' : Over.mk s ⟶ H.X} (hg : RightGood Ω Ω' g h) (hg' : RightGood Ω Ω' g h') :
    h = h' := by
  obtain ⟨p, q, hpq⟩ := hΩ A s g
  have e₁ := hg A s (𝟙 _) p q (by rw [Category.id_comp]; exact hpq)
  have e₂ := hg' A s (𝟙 _) p q (by rw [Category.id_comp]; exact hpq)
  rw [Category.id_comp] at e₁ e₂
  exact mul_left_cancel (e₁.trans e₂.symm)

/-- **Weil's generic-line argument.** Right-good pairs are closed under multiplication. The
line over `B` from `x` (at `X = 0`) to a cell point `p` carrying the first factor into the cell
(at `X = 1`) lifts both partial products to the cell over the local rings of the line at
`X = 0` and `X = 1`; the two hypotheses are applied over a faithfully flat local extension
with algebraically closed residue field of the local ring at the generic point of the closed
fibre, and the resulting relation descends to `X = 0`. -/
theorem RightGood.mul [IsAffine H.X.left] [IsOpenImmersion Ω.left] (hΩ : HasCellFactors Ω)
    {Z : Over (Spec (CommRingCat.of R))} {g₁ g₂ : Z ⟶ G.X} {h₁ h₂ : Z ⟶ H.X}
    (hg₁ : RightGood Ω Ω' g₁ h₁) (hg₂ : RightGood Ω Ω' g₂ h₂) :
    RightGood Ω Ω' (g₁ * g₂) (h₁ * h₂) := by
  intro B _ _ _ sB f x y hxy
  have : Mono Ω := Over.mono_of_mono_left Ω
  obtain ⟨p, q, hpq⟩ := hΩ B sB (f ≫ g₁)
  rw [MonObj.comp_mul, ← mul_assoc] at hxy ⊢
  -- the line from `x` (at `X = 0`) to `p` (at `X = 1`)
  let V : Fin m → B[X] := fun k => lineCoeff (negVal x k) (negVal p k)
  let T : I → B[X] := fun j => lineCoeff (torusVal x j : B) (torusVal p j : B)
  let W : Fin n → B[X] := fun k => lineCoeff (posVal x k) (posVal p k)
  have hu₀ : ∀ j, IsUnit (algebraMap B[X] (AtPoint B 0) (T j)) := fun j =>
    IsLocalization.map_units (AtPoint B 0)
      (⟨T j, lineCoeff_notMem_pointIdeal_zero (torusVal x j).isUnit _⟩ :
        (pointIdeal B 0).primeCompl)
  have hu₁ : ∀ j, IsUnit (algebraMap B[X] (AtPoint B 1) (T j)) := fun j =>
    IsLocalization.map_units (AtPoint B 1)
      (⟨T j, lineCoeff_notMem_pointIdeal_one _ (torusVal p j).isUnit⟩ :
        (pointIdeal B 1).primeCompl)
  have huG : ∀ j, IsUnit (algebraMap B[X] (Generic B) (T j)) := fun j =>
    IsLocalization.map_units (Generic B)
      (⟨T j, lineCoeff_notMem_genericIdeal (torusVal x j).isUnit _⟩ :
        (genericIdeal B).primeCompl)
  have hue₀ : ∀ j, IsUnit (Polynomial.evalRingHom (0 : B) (T j)) := fun j => by
    simpa only [T, Polynomial.coe_evalRingHom, eval_zero_lineCoeff] using (torusVal x j).isUnit
  have hue₁ : ∀ j, IsUnit (Polynomial.evalRingHom (1 : B) (T j)) := fun j => by
    simpa only [T, Polynomial.coe_evalRingHom, eval_one_lineCoeff] using (torusVal p j).isUnit
  obtain ⟨B'', _, _, _, _, _, _⟩ :=
    Langlands.CommutativeAlgebra.exists_faithfullyFlat_local_algClosed_residue (Generic B)
  let ψ := (algebraMap (Generic B) B'').comp (algebraMap B[X] (Generic B))
  have hu : ∀ j, IsUnit (ψ (T j)) := fun j => (huG j).map (algebraMap (Generic B) B'')
  -- test objects
  let s₀ := Spec.map (CommRingCat.ofHom ((algebraMap B[X] (AtPoint B 0)).comp C)) ≫ sB
  let s₁ := Spec.map (CommRingCat.ofHom ((algebraMap B[X] (AtPoint B 1)).comp C)) ≫ sB
  let s'' := Spec.map (CommRingCat.ofHom (ψ.comp C)) ≫ sB
  let b₀ : Over.mk s₀ ⟶ Over.mk sB := specHom ((algebraMap B[X] (AtPoint B 0)).comp C) rfl
  let b₁ : Over.mk s₁ ⟶ Over.mk sB := specHom ((algebraMap B[X] (AtPoint B 1)).comp C) rfl
  let b'' : Over.mk s'' ⟶ Over.mk sB := specHom (ψ.comp C) rfl
  let z₀ := linePoint V T W (algebraMap B[X] (AtPoint B 0)) hu₀ s₀
  let z₁ := linePoint V T W (algebraMap B[X] (AtPoint B 1)) hu₁ s₁
  let z'' := linePoint V T W ψ hu s''
  let E₀ : Over.mk sB ⟶ Over.mk s₀ := specHom (evalAt 0) (specMap_evalAt_comp 0 sB)
  let E₁ : Over.mk sB ⟶ Over.mk s₁ := specHom (evalAt 1) (specMap_evalAt_comp 1 sB)
  let κ₀ := (algebraMap (Generic B) B'').comp (toGeneric (0 : B))
  let κ₁ := (algebraMap (Generic B) B'').comp (toGeneric (1 : B))
  have hκ₀ : κ₀.comp (algebraMap B[X] (AtPoint B 0)) = ψ := by
    rw [RingHom.comp_assoc, toGeneric_comp]
  have hκ₁ : κ₁.comp (algebraMap B[X] (AtPoint B 1)) = ψ := by
    rw [RingHom.comp_assoc, toGeneric_comp]
  have hs₀ : Spec.map (CommRingCat.ofHom κ₀) ≫ s₀ = s'' := by
    dsimp only [s₀, s'']
    rw [specMap_comp_specMap, ← RingHom.comp_assoc, hκ₀]
  have hs₁ : Spec.map (CommRingCat.ofHom κ₁) ≫ s₁ = s'' := by
    dsimp only [s₁, s'']
    rw [specMap_comp_specMap, ← RingHom.comp_assoc, hκ₁]
  let k₀ : Over.mk s'' ⟶ Over.mk s₀ := specHom κ₀ hs₀
  let k₁ : Over.mk s'' ⟶ Over.mk s₁ := specHom κ₁ hs₁
  -- compatibilities
  have hb₀ : E₀ ≫ b₀ = 𝟙 _ :=
    (specHom_comp_eq (by rw [← RingHom.comp_assoc, evalAt_comp_C]) _ _).trans (specHom_id _)
  have hb₁ : E₁ ≫ b₁ = 𝟙 _ :=
    (specHom_comp_eq (by rw [← RingHom.comp_assoc, evalAt_comp_C]) _ _).trans (specHom_id _)
  have hkb₀ : k₀ ≫ b₀ = b'' := specHom_comp_eq (by rw [← RingHom.comp_assoc, hκ₀]) _ _
  have hkb₁ : k₁ ≫ b₁ = b'' := specHom_comp_eq (by rw [← RingHom.comp_assoc, hκ₁]) _ _
  have hz₀ : E₀ ≫ z₀ = x := by
    dsimp only [E₀, z₀]
    rw [specHom_comp_linePoint V T W (evalAt 0) (evalAt_comp 0) hu₀ hue₀,
      linePoint_eq V T W _ hue₀ sB (negVal x) (torusVal x) (posVal x)
        (fun k => eval_zero_lineCoeff _ _) (fun j => eval_zero_lineCoeff _ _)
        (fun k => eval_zero_lineCoeff _ _)]
    exact eq_specCellPoint x
  have hz₁ : E₁ ≫ z₁ = p := by
    dsimp only [E₁, z₁]
    rw [specHom_comp_linePoint V T W (evalAt 1) (evalAt_comp 1) hu₁ hue₁,
      linePoint_eq V T W _ hue₁ sB (negVal p) (torusVal p) (posVal p)
        (fun k => eval_one_lineCoeff _ _) (fun j => eval_one_lineCoeff _ _)
        (fun k => eval_one_lineCoeff _ _)]
    exact eq_specCellPoint p
  have hkz₀ : k₀ ≫ z₀ = z'' := specHom_comp_linePoint V T W κ₀ hκ₀ hu₀ hu hs₀
  have hkz₁ : k₁ ≫ z₁ = z'' := specHom_comp_linePoint V T W κ₁ hκ₁ hu₁ hu hs₁
  -- lifts into the cell near `X = 0` and `X = 1`
  have hE₀w : E₀ ≫ (z₀ ≫ Ω * (b₀ ≫ f ≫ g₁) * (b₀ ≫ f ≫ g₂)) = y ≫ Ω := by
    rw [MonObj.comp_mul, MonObj.comp_mul, ← Category.assoc E₀ z₀, hz₀,
      ← Category.assoc E₀ b₀ (f ≫ g₁), ← Category.assoc E₀ b₀ (f ≫ g₂), hb₀,
      Category.id_comp, Category.id_comp]
    exact hxy
  have hE₁w : E₁ ≫ (z₁ ≫ Ω * (b₁ ≫ f ≫ g₁)) = q ≫ Ω := by
    rw [MonObj.comp_mul, ← Category.assoc E₁ z₁, hz₁, ← Category.assoc E₁ b₁ (f ≫ g₁), hb₁,
      Category.id_comp]
    exact hpq
  have hk₀ : (z₀ ≫ Ω * (b₀ ≫ f ≫ g₁) * (b₀ ≫ f ≫ g₂)).left
      (IsLocalRing.closedPoint (AtPoint B 0)) ∈ Set.range Ω.left := by
    have hcl : E₀.left (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint (AtPoint B 0) :=
      IsLocalRing.comap_closedPoint (evalAt (0 : B))
    rw [← hcl]
    change (E₀ ≫ (z₀ ≫ Ω * (b₀ ≫ f ≫ g₁) * (b₀ ≫ f ≫ g₂))).left
      (IsLocalRing.closedPoint B) ∈ _
    rw [hE₀w]
    exact ⟨_, rfl⟩
  have hk₁ : (z₁ ≫ Ω * (b₁ ≫ f ≫ g₁)).left
      (IsLocalRing.closedPoint (AtPoint B 1)) ∈ Set.range Ω.left := by
    have hcl : E₁.left (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint (AtPoint B 1) :=
      IsLocalRing.comap_closedPoint (evalAt (1 : B))
    rw [← hcl]
    change (E₁ ≫ (z₁ ≫ Ω * (b₁ ≫ f ≫ g₁))).left (IsLocalRing.closedPoint B) ∈ _
    rw [hE₁w]
    exact ⟨_, rfl⟩
  obtain ⟨c₀, hc₀⟩ := exists_lift_of_localPoint_closedPoint_mem Ω _ hk₀
  obtain ⟨d₁, hd₁⟩ := exists_lift_of_localPoint_closedPoint_mem Ω _ hk₁
  -- the two relations over the closed-residue extension of the generic point
  have hY₁ : (z'' ≫ Ω) * ((b'' ≫ f) ≫ g₁) = (k₁ ≫ d₁) ≫ Ω := by
    rw [Category.assoc k₁, hd₁, MonObj.comp_mul, ← Category.assoc k₁ z₁, hkz₁,
      ← Category.assoc k₁ b₁, hkb₁, Category.assoc]
  have e₁ := hg₁ B'' s'' (b'' ≫ f) z'' (k₁ ≫ d₁) hY₁
  have hC₀ : ((k₁ ≫ d₁) ≫ Ω) * ((b'' ≫ f) ≫ g₂) = (k₀ ≫ c₀) ≫ Ω := by
    rw [← hY₁, Category.assoc k₀, hc₀, MonObj.comp_mul, MonObj.comp_mul,
      ← Category.assoc k₀ z₀, hkz₀, ← Category.assoc k₀ b₀ (f ≫ g₁),
      ← Category.assoc k₀ b₀ (f ≫ g₂), hkb₀, Category.assoc, Category.assoc]
  have e₂ := hg₂ B'' s'' (b'' ≫ f) (k₁ ≫ d₁) (k₀ ≫ c₀) hC₀
  have e : k₀ ≫ (z₀ ≫ Ω' * (b₀ ≫ f ≫ h₁) * (b₀ ≫ f ≫ h₂)) = k₀ ≫ (c₀ ≫ Ω') := by
    rw [MonObj.comp_mul, MonObj.comp_mul, ← Category.assoc k₀ z₀, hkz₀,
      ← Category.assoc k₀ b₀ (f ≫ h₁), ← Category.assoc k₀ b₀ (f ≫ h₂), hkb₀,
      ← Category.assoc k₀ c₀, ← e₂, ← e₁, Category.assoc, Category.assoc]
  -- descent to the local ring at `X = 0`
  have hinj : Function.Injective κ₀ :=
    (FaithfulSMul.algebraMap_injective (Generic B) B'').comp (toGeneric_injective 0)
  have e' : z₀ ≫ Ω' * (b₀ ≫ f ≫ h₁) * (b₀ ≫ f ≫ h₂) = c₀ ≫ Ω' := by
    apply Over.OverMorphism.ext
    apply CellGluing.hom_ext_of_injective_specMap κ₀ hinj
    exact congrArg CommaMorphism.left e
  -- specialization to `X = 0`
  have hy : E₀ ≫ c₀ = y := by
    apply (cancel_mono Ω).mp
    rw [Category.assoc, hc₀, hE₀w]
  have e'' := congrArg (E₀ ≫ ·) e'
  rw [MonObj.comp_mul, MonObj.comp_mul, ← Category.assoc E₀ z₀, hz₀,
    ← Category.assoc E₀ b₀ (f ≫ h₁), ← Category.assoc E₀ b₀ (f ≫ h₂), hb₀,
    Category.id_comp, Category.id_comp, ← Category.assoc, hy] at e''
  exact e''

end RightGood

section Generators

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u} {m n : ℕ}
  {G H : GroupScheme (Spec (CommRingCat.of R))}

/-- Right translation by torus points carries relations between `G`-cell points to the same
relations between `H`-cell points, over local test rings with separably closed residue
fields. -/
def TorusRelations (Ω : cellObj R I m n ⟶ G.X) (Ω' : cellObj R I m n ⟶ H.X)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H) : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) (x y : Over.mk s ⟶ cellObj R I m n)
    (t : Over.mk s ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X),
    (x ≫ Ω) * (t ≫ i.hom.hom) = y ≫ Ω → (x ≫ Ω') * (t ≫ i'.hom.hom) = y ≫ Ω'

/-- Right translation by root points carries relations between `G`-cell points to the same
relations between `H`-cell points, over local test rings with separably closed residue
fields. -/
def RootRelations (Ω : cellObj R I m n ⟶ G.X) (Ω' : cellObj R I m n ⟶ H.X)
    (u : J → (Ga R ⟶ G)) (u' : J → (Ga R ⟶ H)) : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) (x y : Over.mk s ⟶ cellObj R I m n)
    (α : J) (c : Γ((Over.mk s).left, ⊤)),
    (x ≫ Ω) * rootPoint (u α) (Over.mk s) c = y ≫ Ω →
      (x ≫ Ω') * rootPoint (u' α) (Over.mk s) c = y ≫ Ω'

variable {Ω : cellObj R I m n ⟶ G.X} {Ω' : cellObj R I m n ⟶ H.X}

theorem rightGood_torus {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H} (hT : TorusRelations Ω Ω' i i')
    {Z : Over (Spec (CommRingCat.of R))} (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) :
    RightGood Ω Ω' (t ≫ i.hom.hom) (t ≫ i'.hom.hom) := by
  intro B _ _ _ sB f x y hxy
  rw [← Category.assoc] at hxy ⊢
  exact hT B sB x y (f ≫ t) hxy

theorem rightGood_rootPoint {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}
    (hR : RootRelations Ω Ω' u u') {Z : Over (Spec (CommRingCat.of R))} (α : J)
    (c : Γ(Z.left, ⊤)) : RightGood Ω Ω' (rootPoint (u α) Z c) (rootPoint (u' α) Z c) := by
  intro B _ _ _ sB f x y hxy
  rw [comp_rootPoint] at hxy ⊢
  exact hR B sB x y α _ hxy

theorem rightGood_orderedProduct [IsAffine H.X.left] [IsOpenImmersion Ω.left]
    (hΩ : HasCellFactors Ω) {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}
    (hR : RootRelations Ω Ω' u u') {Z : Over (Spec (CommRingCat.of R))} {r : ℕ}
    (e : Fin r → J) (c : Fin r → Γ(Z.left, ⊤)) :
    RightGood Ω Ω' (orderedProduct u e Z c) (orderedProduct u' e Z c) := by
  have : Mono Ω := Over.mono_of_mono_left Ω
  unfold orderedProduct
  induction r with
  | zero =>
    rw [List.ofFn_zero, List.ofFn_zero, List.prod_nil, List.prod_nil]
    exact rightGood_one
  | succ r ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    exact (rightGood_rootPoint hR (e 0) (c 0)).mul hΩ
      (ih (fun k => e k.succ) (fun k => c k.succ))

variable {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H} {u : J → (Ga R ⟶ G)}
  {u' : J → (Ga R ⟶ H)} {neg : Fin m → J} {pos : Fin n → J}

/-- For a reductive group with open big cell, every local-ring point is carried into the cell
by left multiplication with a cell point. -/
theorem hasCellFactors_cellMap (hG : IsReductive G) [IsOpenImmersion (cellMap i u neg pos).left] :
    HasCellFactors (cellMap i u neg pos) := by
  intro A _ _ _ s g
  obtain ⟨x, y, hxy⟩ := exists_inverse_cell_factors hG i u neg pos s g
  exact ⟨x, y, by rw [hxy, mul_inv_cancel_left]⟩

/-- Cell points of `G` and the corresponding cell points of `H` form right-good pairs. -/
theorem rightGood_cellMap [IsAffine H.X.left] [IsOpenImmersion (cellMap i u neg pos).left]
    (hΩ : HasCellFactors (cellMap i u neg pos))
    (hT : TorusRelations (cellMap i u neg pos) (cellMap i' u' neg pos) i i')
    (hR : RootRelations (cellMap i u neg pos) (cellMap i' u' neg pos) u u')
    {Z : Over (Spec (CommRingCat.of R))} (x : Z ⟶ cellObj R I m n) :
    RightGood (cellMap i u neg pos) (cellMap i' u' neg pos) (x ≫ cellMap i u neg pos)
      (x ≫ cellMap i' u' neg pos) := by
  rw [comp_cellMap, comp_cellMap, cellPoint, cellPoint]
  exact ((rightGood_orderedProduct hΩ hR neg (negCoord x)).mul hΩ
    (rightGood_torus hT (torusCoord x))).mul hΩ (rightGood_orderedProduct hΩ hR pos (posCoord x))

/-- Every point of `G` over a local test ring with separably closed residue field has a
right-good partner in `H`. -/
theorem exists_rightGood (hG : IsReductive G) [IsAffine H.X.left]
    [IsOpenImmersion (cellMap i u neg pos).left]
    (hT : TorusRelations (cellMap i u neg pos) (cellMap i' u' neg pos) i i')
    (hR : RootRelations (cellMap i u neg pos) (cellMap i' u' neg pos) u u')
    {A : Type u} [CommRing A] [IsLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) (g : Over.mk s ⟶ G.X) :
    ∃ h, RightGood (cellMap i u neg pos) (cellMap i' u' neg pos) g h := by
  have hΩ : HasCellFactors (cellMap i u neg pos) := hasCellFactors_cellMap hG
  obtain ⟨x, y, rfl⟩ := exists_inverse_cell_factors hG i u neg pos s g
  exact ⟨_, (rightGood_cellMap hΩ hT hR x).inv.mul hΩ (rightGood_cellMap hΩ hT hR y)⟩

/-- **Big-cell gluing from generator relations.** If right translation by torus points and by
root points carries relations between cell points of `G` to the same relations between cell
points of `H`, over local test rings with separably closed residue fields, then `G` and `H`
are isomorphic by an isomorphism matching the two big-cell maps. -/
theorem exists_iso_of_generatorRelations (hG : IsReductive G) (hH : IsReductive H)
    [IsOpenImmersion (cellMap i u neg pos).left] [IsOpenImmersion (cellMap i' u' neg pos).left]
    (hT : TorusRelations (cellMap i u neg pos) (cellMap i' u' neg pos) i i')
    (hR : RootRelations (cellMap i u neg pos) (cellMap i' u' neg pos) u u') :
    ∃ ψ : G ≅ H, cellMap i u neg pos ≫ ψ.hom.hom.hom = cellMap i' u' neg pos := by
  have := hH.isAffineHom
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : Mono (cellMap i u neg pos) := Over.mono_of_mono_left _
  have hΩ : HasCellFactors (cellMap i u neg pos) := hasCellFactors_cellMap hG
  apply exists_iso_of_closedResidueLocalRingPoints hG hH neg pos
  intro A _ _ _ s
  have hP : ∀ g : Over.mk s ⟶ G.X,
      ∃ h, RightGood (cellMap i u neg pos) (cellMap i' u' neg pos) g h :=
    fun g => exists_rightGood hG hT hR s g
  let Ψ : (Over.mk s ⟶ G.X) →* (Over.mk s ⟶ H.X) :=
    { toFun := fun g => Classical.choose (hP g)
      map_one' := RightGood.unique hΩ (Classical.choose_spec (hP 1)) rightGood_one
      map_mul' := fun g₁ g₂ => RightGood.unique hΩ (Classical.choose_spec (hP (g₁ * g₂)))
        ((Classical.choose_spec (hP g₁)).mul hΩ (Classical.choose_spec (hP g₂))) }
  have hΨ : ∀ g h, RightGood (cellMap i u neg pos) (cellMap i' u' neg pos) g h → Ψ g = h :=
    fun g _ hgh => RightGood.unique hΩ (Classical.choose_spec (hP g)) hgh
  have hi : ∀ t : Over.mk s ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X,
      Ψ (t ≫ i.hom.hom) = t ≫ i'.hom.hom := fun t => hΨ _ _ (rightGood_torus hT t)
  have hu : ∀ (α : J) (c : Γ((Over.mk s).left, ⊤)),
      Ψ (rootPoint (u α) (Over.mk s) c) = rootPoint (u' α) (Over.mk s) c :=
    fun α c => hΨ _ _ (rightGood_rootPoint hR α c)
  exact ⟨MulEquiv.ofBijective Ψ (pointHom_bijective_of_matches hG hH neg pos s Ψ hi hu), hi, hu⟩

end Generators

section TorusAction

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u} {m n : ℕ}

/-- The value of the exponent character `ch` of the split torus at a torus point. -/
def torusChar (ch : I → ℤ) (Z : Over (Spec (CommRingCat.of R)))
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) : Γ(Z.left, ⊤) :=
  VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
    (splitTorus.exponentCharacter _ I ch) Z t

theorem isUnit_torusChar (ch : I → ℤ) (Z : Over (Spec (CommRingCat.of R)))
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) : IsUnit (torusChar ch Z t) :=
  Units.isUnit _

/-- The torus acts on each `u α` through the exponent character `ch α`, as in the
equivariance condition of a root parametrization. -/
def TorusEquivariant {G : GroupScheme (Spec (CommRingCat.of R))}
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (ch : J → I → ℤ) (u : J → (Ga R ⟶ G)) :
    Prop :=
  ∀ (α : J) (Z : Over (Spec (CommRingCat.of R)))
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (c : Γ(Z.left, ⊤)),
    (t ≫ i.hom.hom) * rootPoint (u α) Z c * (t ≫ i.hom.hom)⁻¹ =
      rootPoint (u α) Z (torusChar (ch α) Z t * c)

variable {G : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {ch : J → I → ℤ} {u : J → (Ga R ⟶ G)}

theorem rootPoint_mul_torus (hu : TorusEquivariant i ch u) (α : J)
    {Z : Over (Spec (CommRingCat.of R))} (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X)
    (c : Γ(Z.left, ⊤)) :
    rootPoint (u α) Z c * (t ≫ i.hom.hom) =
      (t ≫ i.hom.hom) * rootPoint (u α) Z (Ring.inverse (torusChar (ch α) Z t) * c) := by
  have h := hu α Z t (Ring.inverse (torusChar (ch α) Z t) * c)
  rw [← mul_assoc, Ring.mul_inverse_cancel _ (isUnit_torusChar _ _ _), one_mul] at h
  rw [← h, inv_mul_cancel_right]

theorem orderedProduct_mul_torus (hu : TorusEquivariant i ch u) {r : ℕ} (e : Fin r → J)
    {Z : Over (Spec (CommRingCat.of R))} (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X)
    (c : Fin r → Γ(Z.left, ⊤)) :
    orderedProduct u e Z c * (t ≫ i.hom.hom) =
      (t ≫ i.hom.hom) *
        orderedProduct u e Z (fun k => Ring.inverse (torusChar (ch (e k)) Z t) * c k) := by
  unfold orderedProduct
  induction r with
  | zero => simp only [List.ofFn_zero, List.prod_nil, one_mul, mul_one]
  | succ r ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, mul_assoc,
      ih (fun k => e k.succ) (fun k => c k.succ), ← mul_assoc, rootPoint_mul_torus hu,
      mul_assoc]

variable {neg : Fin m → J} {pos : Fin n → J}

/-- Right translation of a cell point by a torus point, computed in the cell coordinates. -/
theorem comp_cellMap_mul_torus (hu : TorusEquivariant i ch u)
    {Z : Over (Spec (CommRingCat.of R))} (x z : Z ⟶ cellObj R I m n)
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (hv : negCoord z = negCoord x)
    (ht : torusCoord z = torusCoord x * t)
    (hw : posCoord z = fun k => Ring.inverse (torusChar (ch (pos k)) Z t) * posCoord x k) :
    (x ≫ cellMap i u neg pos) * (t ≫ i.hom.hom) = z ≫ cellMap i u neg pos := by
  rw [comp_cellMap, comp_cellMap, cellPoint, cellPoint, hv, ht, hw, MonObj.mul_comp,
    mul_assoc _ (orderedProduct u pos Z (posCoord x)), orderedProduct_mul_torus hu pos t (posCoord x)]
  simp only [mul_assoc]

variable {H : GroupScheme (Spec (CommRingCat.of R))}
  {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H} {u' : J → (Ga R ⟶ H)}

/-- Torus equivariance through common exponent characters gives the torus relations. -/
theorem torusRelations_of_equivariant [Mono (cellMap i u neg pos)]
    (hu : TorusEquivariant i ch u) (hu' : TorusEquivariant i' ch u') :
    TorusRelations (cellMap i u neg pos) (cellMap i' u' neg pos) i i' := by
  intro A _ _ _ s x y t hxy
  obtain ⟨z, hz⟩ := (LocalSplitBigCell.coordTriple_bijective R I m n (Over.mk s)).2
    (negCoord x, torusCoord x * t,
      fun k => Ring.inverse (torusChar (ch (pos k)) (Over.mk s) t) * posCoord x k)
  have hv : negCoord z = negCoord x := congrArg Prod.fst hz
  have ht : torusCoord z = torusCoord x * t := congrArg (fun q => q.2.1) hz
  have hw : posCoord z =
      fun k => Ring.inverse (torusChar (ch (pos k)) (Over.mk s) t) * posCoord x k :=
    congrArg (fun q => q.2.2) hz
  have hzy : z = y := (cancel_mono (cellMap i u neg pos)).mp
    ((comp_cellMap_mul_torus hu x z t hv ht hw).symm.trans hxy)
  rw [comp_cellMap_mul_torus hu' x z t hv ht hw, hzy]

/-- **Big-cell gluing from root relations.** For torus-equivariant families with common
exponent characters, the root relations alone glue `G` and `H`. -/
theorem exists_iso_of_rootRelations (hG : IsReductive G) (hH : IsReductive H)
    [IsOpenImmersion (cellMap i u neg pos).left] [IsOpenImmersion (cellMap i' u' neg pos).left]
    (hu : TorusEquivariant i ch u) (hu' : TorusEquivariant i' ch u')
    (hR : RootRelations (cellMap i u neg pos) (cellMap i' u' neg pos) u u') :
    ∃ ψ : G ≅ H, cellMap i u neg pos ≫ ψ.hom.hom.hom = cellMap i' u' neg pos := by
  have : Mono (cellMap i u neg pos) := Over.mono_of_mono_left _
  exact exists_iso_of_generatorRelations hG hH (torusRelations_of_equivariant hu hu') hR

end TorusAction

end LocalSplitCell

/-- Big-cell gluing over an arbitrary commutative ring from root relations: for root families
on which the common split torus acts through common exponent characters, it suffices that
right translation by root points transfers relations between big-cell points, over local test
rings with separably closed residue fields. -/
def LocalSplitGeneratorRelationIsomorphismStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Type u) [Fintype I] (J : Type u)
    (G H : GroupScheme (Spec (CommRingCat.of R))),
    IsReductive G → IsReductive H →
    ∀ (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
      (i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H)
      (u : J → (LocalSplitCell.Ga R ⟶ G)) (u' : J → (LocalSplitCell.Ga R ⟶ H))
      (ch : J → I → ℤ) (m n : ℕ) (neg : Fin m → J) (pos : Fin n → J),
      IsOpenImmersion (LocalSplitCell.cellMap i u neg pos).left →
      IsOpenImmersion (LocalSplitCell.cellMap i' u' neg pos).left →
      (∀ (α : J) (Z : Over (Spec (CommRingCat.of R)))
        (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (c : Γ(Z.left, ⊤)),
        (t ≫ i.hom.hom) * LocalSplitCell.rootPoint (u α) Z c * (t ≫ i.hom.hom)⁻¹ =
          LocalSplitCell.rootPoint (u α) Z
            (VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
              (splitTorus.exponentCharacter _ I (ch α)) Z t * c)) →
      (∀ (α : J) (Z : Over (Spec (CommRingCat.of R)))
        (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (c : Γ(Z.left, ⊤)),
        (t ≫ i'.hom.hom) * LocalSplitCell.rootPoint (u' α) Z c * (t ≫ i'.hom.hom)⁻¹ =
          LocalSplitCell.rootPoint (u' α) Z
            (VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
              (splitTorus.exponentCharacter _ I (ch α)) Z t * c)) →
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)]
        (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
        (x y : Over.mk s ⟶ LocalSplitCell.cellObj R I m n) (α : J) (c : Γ((Over.mk s).left, ⊤)),
        (x ≫ LocalSplitCell.cellMap i u neg pos) * LocalSplitCell.rootPoint (u α) (Over.mk s) c =
            y ≫ LocalSplitCell.cellMap i u neg pos →
          (x ≫ LocalSplitCell.cellMap i' u' neg pos) *
              LocalSplitCell.rootPoint (u' α) (Over.mk s) c =
            y ≫ LocalSplitCell.cellMap i' u' neg pos) →
      ∃ ψ : G ≅ H, LocalSplitCell.cellMap i u neg pos ≫ ψ.hom.hom.hom =
        LocalSplitCell.cellMap i' u' neg pos

/-- Root relations for right translation suffice for big-cell gluing of torus-equivariant
root families. -/
theorem localSplitGeneratorRelationIsomorphism :
    LocalSplitGeneratorRelationIsomorphismStatement.{u} := by
  intro R _ I _ J G H hG hH i i' u u' ch m n neg pos hj hν hu hu' hR
  let := hj
  let := hν
  exact LocalSplitCell.exists_iso_of_rootRelations (ch := ch) hG hH hu hu' hR

end Langlands.GroupScheme
