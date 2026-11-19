import Langlands.Geometry.FormalGroup.DivisionOrderAtlasRationalTwist

/-! # Special twists compatible with the embedded integer subfield -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v w q r s

namespace Langlands.FormalGroup.ModuleLaw.OrderAction

variable {O : Type u} [CommRing O] {A : Type v} [Ring A] [Algebra O A]
variable {R : Type w} [CommRing R] [Algebra O R]
variable {C : Type r} [CommRing C] {κ : Type q} [CommRing κ]
variable {σ : Type} [Finite σ] {M : ModuleLaw O R σ}
variable {E E' : OrderAction A M} {j : C →+* A} {d : ℕ} {φ : R →+* κ}

/-- Comparing the restricted actions through a ring automorphism precomposes every character. -/
def TangentCharacterDecomposition.ofRestrictedAction
    (h : E.TangentCharacterDecomposition j d φ) (β : C ≃+* C)
    (hβ : ∀ c, E'.action (j c) = E.action (j (β c))) :
    E'.TangentCharacterDecomposition j d φ where
  characters i := (h.characters i).comp β.toRingHom
  distinct := by
    intro i k hik
    apply h.distinct
    apply RingHom.ext
    intro c
    obtain ⟨a, rfl⟩ := β.surjective c
    exact DFunLike.congr_fun hik a
  coordinates := h.coordinates
  diagonalizes c x i := by
    change h.coordinates ((E'.action (j c)).fiberTangent φ x) i =
      h.characters i (β c) * h.coordinates x i
    rw [hβ]
    exact h.diagonalizes (β c) x i

/-- The restricted-action comparison preserves the geometric distinct-character condition. -/
theorem HasGeometricTangentCharacters.ofRestrictedAction
    (h : E.HasGeometricTangentCharacters.{u, v, w, q, r} j d) (β : C ≃+* C)
    (hβ : ∀ c, E'.action (j c) = E.action (j (β c))) :
    E'.HasGeometricTangentCharacters.{u, v, w, q, r} j d := by
  intro F _ _ ψ
  obtain ⟨e⟩ := h F ψ
  exact ⟨e.ofRestrictedAction β hβ⟩

end Langlands.FormalGroup.ModuleLaw.OrderAction

namespace Langlands.FormalGroup.LocalDivision

open CategoryTheory ValuativeRel ModuleLaw

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

/-- On the embedded integers, inverse conjugation factors through a subfield automorphism
followed by inverse conjugation by an integral unit. -/
def ConjugationSubfieldFactorization (g : Dˣ) : Prop :=
  ∃ (a : (IntegerRing K D)ˣ) (β : SubfieldIntegerRing K D ι ≃+* SubfieldIntegerRing K D ι),
    ∀ c, conjugation K D g (subfieldIntegerInclusion K D ι c) =
      conjugation K D (integerUnit K D a) (subfieldIntegerInclusion K D ι (β c))

/-- Every integer-order unit satisfies the comparison by the identity on the embedded integers. -/
theorem conjugationSubfieldFactorization_integerUnit (a : (IntegerRing K D)ˣ) :
    ConjugationSubfieldFactorization K D ι (integerUnit K D a) :=
  ⟨a, RingEquiv.refl _, fun _ => rfl⟩

/-- A unit that restricts to the given automorphism of the embedded integers satisfies the comparison. -/
theorem conjugationSubfieldFactorization_of_normalizes (g : Dˣ)
    (β : SubfieldIntegerRing K D ι ≃+* SubfieldIntegerRing K D ι)
    (h : ∀ c, conjugation K D g (subfieldIntegerInclusion K D ι c) =
      subfieldIntegerInclusion K D ι (β c)) :
    ConjugationSubfieldFactorization K D ι g := by
  refine ⟨1, β, fun c => ?_⟩
  change conjugation K D g (subfieldIntegerInclusion K D ι c) =
    conjugation K D 1 (subfieldIntegerInclusion K D ι (β c))
  rw [conjugation_one]
  exact h c

variable {K D ι}
variable {R S : Type v} [CommRing R] [Algebra 𝒪[K] R]
  [CommRing S] [Algebra 𝒪[K] S]

attribute [local instance] coefficientAlgebra coefficientScalarTower

private theorem geometricCharacters_twist {σ : Type} [Finite σ]
    {M : ModuleLaw 𝒪[K] R σ} {E : OrderAction (IntegerRing K D) M} {d : ℕ}
    (h : E.HasGeometricTangentCharacters.{u, u, v, max u v, s}
      (subfieldIntegerInclusion K D ι).toRingHom d)
    (g : Dˣ) (hg : ConjugationSubfieldFactorization K D ι g) :
    (twist K D E g).HasGeometricTangentCharacters.{u, u, v, max u v, s}
      (subfieldIntegerInclusion K D ι).toRingHom d := by
  obtain ⟨a, β, hβ⟩ := hg
  have h₁ := h.ofIso (twistUnitIso K D E a)
  apply h₁.ofRestrictedAction β
  intro c
  exact congrArg (fun x => E.action x) (hβ c)

namespace SpecialModule

/-- The special coordinate twist when the embedded integer actions satisfy the comparison. -/
def twistOfSubfieldFactorization (X : SpecialModule K D ι R) (g : Dˣ)
    (hg : ConjugationSubfieldFactorization K D ι g) : SpecialModule K D ι R where
  formalModule := X.formalModule
  order := twist K D X.order g
  unramified := X.unramified
  tangent := geometricCharacters_twist X.tangent g hg

theorem twistOfSubfieldFactorization_height_iff (X : SpecialModule K D ι R) (g : Dˣ)
    (hg : ConjugationSubfieldFactorization K D ι g) (π : 𝒪[K]) :
    (X.twistOfSubfieldFactorization g hg).HasHeightSquared π ↔ X.HasHeightSquared π := Iff.rfl

theorem twistOfSubfieldFactorization_map (X : SpecialModule K D ι R) (g : Dˣ)
    (hg : ConjugationSubfieldFactorization K D ι g) (θ : R →ₐ[𝒪[K]] S) :
    (X.twistOfSubfieldFactorization g hg).mapSameUniverse θ =
      (X.mapSameUniverse θ).twistOfSubfieldFactorization g hg := rfl

end SpecialModule

namespace SpecialAtlas

/-- The actual special atlas with each chart action conjugated by the permitted division unit. -/
def twistOfSubfieldFactorization (X : SpecialAtlas K D ι R) (g : Dˣ)
    (hg : ConjugationSubfieldFactorization K D ι g) : SpecialAtlas K D ι R where
  atlas := X.atlas
  order := atlasTwist K D X.order g
  unramified := X.unramified
  tangent b := geometricCharacters_twist (X.tangent b) g hg

/-- The target twist comes with the original whole atlas quasi-isogeny. -/
def twistQuasiIsogenyOfSubfieldFactorization (X : SpecialAtlas K D ι R) (g : Dˣ)
    (hg : ConjugationSubfieldFactorization K D ι g) :
    BasicAtlas.OrderAction.QuasiIsogeny K X.order (X.twistOfSubfieldFactorization g hg).order rfl :=
  atlasTwistQuasiIsogeny K D X.order g

theorem twistOfSubfieldFactorization_height_iff (X : SpecialAtlas K D ι R) (g : Dˣ)
    (hg : ConjugationSubfieldFactorization K D ι g) (π : 𝒪[K]) :
    (X.twistOfSubfieldFactorization g hg).HasHeightSquared π ↔ X.HasHeightSquared π := Iff.rfl

theorem twistOfSubfieldFactorization_baseChange (X : SpecialAtlas K D ι R) (g : Dˣ)
    (hg : ConjugationSubfieldFactorization K D ι g) (B : CommAlgCat.{v} R) :
    (X.twistOfSubfieldFactorization g hg).baseChange B =
      (X.baseChange B).twistOfSubfieldFactorization g hg := rfl

theorem twistOfSubfieldFactorization_integerUnit (X : SpecialAtlas K D ι R)
    (a : (IntegerRing K D)ˣ)
    (ha : ConjugationSubfieldFactorization K D ι (integerUnit K D a)) :
    X.twistOfSubfieldFactorization (integerUnit K D a) ha = X.twistIntegerUnit a := rfl

namespace HeightSquaredAtlas

/-- Carry the unchanged scalar-kernel rank certificate to the conjugated special atlas. -/
def twistOfSubfieldFactorization {π : 𝒪[K]}
    (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π) (g : Dˣ)
    (hg : ConjugationSubfieldFactorization K D ι g) :
    HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π :=
  ⟨X.val.twistOfSubfieldFactorization g hg, X.property⟩

end HeightSquaredAtlas
end SpecialAtlas
end Langlands.FormalGroup.LocalDivision
