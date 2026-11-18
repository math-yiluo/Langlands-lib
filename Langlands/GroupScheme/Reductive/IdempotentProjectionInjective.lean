import Langlands.GroupScheme.Reductive.GeometricNontrivial
import Langlands.GroupScheme.Reductive.AlmostSimple
import Langlands.GroupScheme.AffineIdempotentPoints

/-! # Factor projections of a fibrewise nontrivial group determine the idempotent -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Langlands.GroupScheme.IdempotentProjection

open IdempotentPoints

variable {B : Type u} [CommRing B] (G : GroupScheme (Spec (CommRingCat.of B)))

section Natural

variable [IsAffine G.X.left] (T : CommAlgCat.{u} (CommRingCat.of B))

/-- The factor projection at an idempotent `e` of `T`, as a natural endomorphism of the group
functor of `G` on `T`-algebras: over `X`, it is `IdempotentPoints.proj G` at the image of `e`. -/
def projNat (e : T) (he : IsIdempotentElem e) :
    Under.forget T ⋙ G.affinePointFunctor ⟶ Under.forget T ⋙ G.affinePointFunctor where
  app X := GrpCat.ofHom (proj G (X.hom.hom e))
  naturality X Y φ := by
    refine GrpCat.ext fun x => ?_
    change proj G (Y.hom.hom e) (G.affinePointMap φ.right x) =
      G.affinePointMap φ.right (proj G (X.hom.hom e) x)
    have hw : φ.right.hom (X.hom.hom e) = Y.hom.hom e :=
      congrArg (fun k : T ⟶ Y.right => k.hom e) (Under.w φ)
    exact (proj_map G φ.right.hom (he.map X.hom.hom) hw x).symm

theorem projNat_app (e : T) (he : IsIdempotentElem e) (X : Under T)
    (x : G.affinePoints X.right) :
    (projNat G T e he).app X x = proj G (X.hom.hom e) x := rfl

end Natural

section Piece

variable {K : Type u} [CommRing K] [Algebra B K]

/-- A `K`-algebra regarded as a `B`-algebra. -/
def resK (R : CommAlgCat.{u} (CommRingCat.of K)) : CommAlgCat.{u} (CommRingCat.of B) :=
  letI : Algebra B R := Algebra.compHom R (algebraMap B K)
  CommAlgCat.of (CommRingCat.of B) R

/-- The ring of an affine scheme over `Spec K`, as a `K`-algebra. -/
def pieceK {S : CommRingCat.{u}} (g : Spec S ⟶ Spec (CommRingCat.of K)) :
    CommAlgCat.{u} (CommRingCat.of K) :=
  letI : Algebra K S := (Spec.preimage g).hom.toAlgebra
  CommAlgCat.of (CommRingCat.of K) S

theorem spec_algebraMap_resK_pieceK {S : CommRingCat.{u}}
    (g : Spec S ⟶ Spec (CommRingCat.of K)) :
    Spec.map (CommRingCat.ofHom (algebraMap B (resK (B := B) (pieceK g)))) =
      g ≫ Spec.map (CommRingCat.ofHom (algebraMap B K)) := by
  change Spec.map (CommRingCat.ofHom (algebraMap B K) ≫ Spec.preimage g) = _
  rw [Spec.map_comp, Spec.map_preimage]

/-- **Affine nontrivial points.** If the pullback of `G` to `Spec K` has a point distinct from
the identity on some test scheme, then `G` has a point distinct from the identity over some
`K`-algebra, regarded as a `B`-algebra. -/
theorem exists_affinePoint_ne_one
    (hG : HasNontrivialPoint
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap B K)))).obj G)) :
    ∃ (R : CommAlgCat.{u} (CommRingCat.of K)) (x : G.affinePoints (resK (B := B) R)), x ≠ 1 := by
  obtain ⟨U, x, hx⟩ := hG
  let b := Spec.map (CommRingCat.ofHom (algebraMap B K))
  let y := baseChangePointsEquiv b G U x
  have hy : y ≠ 1 := fun h => hx ((baseChangePointsEquiv b G U).map_eq_one_iff.mp h)
  let 𝒜 := U.left.affineCover
  let incl : ∀ j, (algSpec (CommRingCat.of B)).obj (op (resK (B := B) (pieceK (𝒜.f j ≫ U.hom)))) ⟶
      (Over.map b).obj U := fun j =>
    Over.homMk (𝒜.f j) (by
      change 𝒜.f j ≫ U.hom ≫ b = Spec.map (CommRingCat.ofHom
        (algebraMap B (resK (B := B) (pieceK (𝒜.f j ≫ U.hom)))))
      rw [spec_algebraMap_resK_pieceK, Category.assoc])
  by_contra hne
  push Not at hne
  apply hy
  apply Over.OverMorphism.ext
  apply Scheme.Cover.hom_ext 𝒜
  intro j
  have h1 := hne (pieceK (𝒜.f j ≫ U.hom)) (incl j ≫ y)
  rw [← MonObj.comp_one (incl j)] at h1
  exact congrArg CommaMorphism.left h1

end Piece

section Injective

variable [IsAffine G.X.left]

/-- One half of the injectivity: if `e (1 - f) ≠ 0`, the projections differ. -/
theorem false_of_proj_eq (hG : IsFibrewiseNontrivial G) {T : CommAlgCat.{u} (CommRingCat.of B)}
    {e f : T} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : ∀ (X : Under T) (x : G.affinePoints X.right),
      proj G (X.hom.hom e) x = proj G (X.hom.hom f) x)
    (hg : e * (1 - f) ≠ 0) : False := by
  have hgi : IsIdempotentElem (e * (1 - f)) := he.mul hf.one_sub
  have hnil : ¬ IsNilpotent (e * (1 - f)) := fun hn => hg (hgi.eq_zero_of_isNilpotent hn)
  rw [nilpotent_iff_mem_prime] at hnil
  push Not at hnil
  obtain ⟨p, hp, hgp⟩ := hnil
  let K := p.ResidueField
  letI : Algebra B K := ((algebraMap T K).comp (algebraMap B T)).toAlgebra
  have hK : algebraMap T K (e * (1 - f)) ≠ 0 := by
    rw [Ne, Ideal.algebraMap_residueField_eq_zero]
    exact hgp
  rw [map_mul] at hK
  have he1 : algebraMap T K e = 1 := by
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp (he.map (algebraMap T K)) with h0 | h1
    · exact absurd (by rw [h0, zero_mul]) hK
    · exact h1
  have hf0 : algebraMap T K f = 0 := by
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp (hf.map (algebraMap T K)) with h0 | h1
    · exact h0
    · exact absurd (by rw [map_sub, map_one, h1, sub_self, mul_zero]) hK
  let b := Spec.map (CommRingCat.ofHom (algebraMap B K))
  have hb : HasNontrivialPoint ((GroupScheme.baseChange b).obj G) :=
    (fieldNontrivial_iff_geometricFiber G b).2 (hG _)
  obtain ⟨R, x, hx⟩ := exists_affinePoint_ne_one G hb
  let ψ : T →ₐ[B] resK (B := B) R :=
    { ((algebraMap K R).comp (algebraMap T K)) with commutes' := fun _ => rfl }
  let φ : T ⟶ resK (B := B) R :=
    ConcreteCategory.ofHom (C := CommAlgCat.{u} (CommRingCat.of B)) (X := T)
      (Y := resK (B := B) R) ψ
  have hx' := h (Under.mk φ) x
  have hφe : (Under.mk φ).hom.hom e = 1 := by
    change algebraMap K R (algebraMap T K e) = 1
    rw [he1, map_one]
  have hφf : (Under.mk φ).hom.hom f = 0 := by
    change algebraMap K R (algebraMap T K f) = 0
    rw [hf0, map_zero]
  rw [hφe, hφf, proj_one, proj_zero] at hx'
  exact hx hx'

/-- **Injectivity of the factor projections.** For a group scheme with affine total space whose
geometric fibres are nontrivial, two idempotents of `T` with the same factor projections over
every `T`-algebra are equal. -/
theorem eq_of_proj_eq (hG : IsFibrewiseNontrivial G) {T : CommAlgCat.{u} (CommRingCat.of B)}
    {e f : T} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : ∀ (X : Under T) (x : G.affinePoints X.right),
      proj G (X.hom.hom e) x = proj G (X.hom.hom f) x) : e = f := by
  by_contra hne
  by_cases h1 : e * (1 - f) = 0
  · by_cases h2 : f * (1 - e) = 0
    · apply hne
      have h1' : e = e * f := by
        rw [mul_sub, mul_one, sub_eq_zero] at h1
        exact h1
      have h2' : f = f * e := by
        rw [mul_sub, mul_one, sub_eq_zero] at h2
        exact h2
      rw [h1', mul_comm, ← h2']
    · exact false_of_proj_eq G hG hf he (fun X x => (h X x).symm) h2
  · exact false_of_proj_eq G hG he hf h h1

/-- The natural factor projections `projNat` are injective in the idempotent. -/
theorem projNat_injective (hG : IsFibrewiseNontrivial G) {T : CommAlgCat.{u} (CommRingCat.of B)}
    {e f : T} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : projNat G T e he = projNat G T f hf) : e = f :=
  eq_of_proj_eq G hG he hf fun X x => by
    rw [← projNat_app G T e he X x, ← projNat_app G T f hf X x, h]

end Injective

/-- Almost-simple geometric fibres are nontrivial: they are noncommutative. -/
theorem isFibrewiseNontrivial_of_isAlmostSimple
    (h : ∀ s, IsAlmostSimple (geometricFiber G s)) : IsFibrewiseNontrivial G := by
  intro s
  by_contra hn
  apply (h s).noncommutative
  intro U x y
  have hall : ∀ z : U ⟶ (geometricFiber G s).X, z = 1 := by
    intro z
    by_contra hz
    exact hn ⟨U, z, hz⟩
  rw [hall x, hall y]

end Langlands.GroupScheme.IdempotentProjection
