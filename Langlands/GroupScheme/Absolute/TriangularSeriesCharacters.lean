import Langlands.GroupScheme.Absolute.TriangularCoordinateCharacters

/-! # Character-linear kernels for the actual triangular quotient series -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TriangularLayer

variable {k : Type u} [Field k] {N : ℕ}
  {D : CommGroupScheme (Spec (CommRingCat.of k))}
  {H : GroupScheme (Spec (CommRingCat.of k))}

/-- The actual ratio character of each genuine enumerated coordinate;
repeated terms use the zero character. -/
def seriesRatioCharacter
    (d : D.toGrp ⟶ GeneralLinear.blockLeviScheme (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ))) (hN : 0 < N) (t : ℕ) : characterLattice D :=
  if h : t % N + t / N + 1 < N then
    diagonalRatioCharacter d ⟨t % N, Nat.mod_lt t hN⟩
      ⟨t % N + t / N + 1, h⟩
  else 0

/-- Actual conjugation on an enumerated full coordinate subgroup. -/
abbrev seriesConjugation
    (j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ))) (t : ℕ) :=
  filtrationConjugation j (t / N) (t % N)

/-- Coordinate equivariance for every enumerated step, including repeated
terms with zero coordinate and zero character. -/
theorem seriesCoordinate_equivariant
    (j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ)))
    (q : H ⟶ D.toGrp)
    (d : D.toGrp ⟶ GeneralLinear.blockLeviScheme (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ)))
    (hfac : q ≫ d = j ≫ GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k) _)
    (hN : 0 < N) (t : ℕ) {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ H.X)
    (x : T ⟶ (seriesScheme
      (j ≫ GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) _) t).X) :
    (seriesConjugation j t).act g x ≫
      (seriesCoordinate
        (j ≫ GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) _) hN t).hom.hom =
    (VectorGroup.weightAction (n := 1) (seriesRatioCharacter d hN t)).act
      (g ≫ q.hom.hom)
      (x ≫ (seriesCoordinate
        (j ≫ GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) _) hN t).hom.hom) := by
  by_cases h : t % N + t / N + 1 < N
  · simp only [seriesCoordinate, seriesRatioCharacter, dite_eq_left h]
    exact filtrationCoordinate_equivariant j q d hfac _ _ _ _ g x
  · simp only [seriesCoordinate, seriesRatioCharacter, dite_eq_right h]
    change (seriesConjugation j t).act g x ≫ 1 =
      (VectorGroup.weightAction (n := 1) (0 : characterLattice D)).act
        (g ≫ q.hom.hom) (x ≫ 1)
    rw [MonObj.comp_one, MonObj.comp_one]
    apply VectorGroup.points_ext
    intro r
    simp

variable [LocallyOfFiniteType H.X.hom] [IsAffineHom H.X.hom]

/-- Every actual adjacent quotient comparison has a character-linear full
kernel, from explicit affine image existence and the original diagonal
factorization. Quotient existence is represented by the supplied terms. -/
theorem seriesComparison_isCharacterLinearKernel
    (himage : AffineHomImageStatement.{u})
    (j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ)))
    (q : H ⟶ D.toGrp)
    (d : D.toGrp ⟶ GeneralLinear.blockLeviScheme (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ)))
    (hfac : q ≫ d = j ≫ GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k) _)
    (hN : 0 < N) (t : ℕ)
    (A : QuotientTerm (SubgroupFunctor.range (seriesHom
      (j ≫ GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) _) t)))
    (B : QuotientTerm (SubgroupFunctor.range (seriesHom
      (j ≫ GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) _) (t + 1))))
    (r : B.quotient ⟶ D.toGrp)
    [QuasiCompact r.hom.hom.left] [Flat r.hom.hom.left] [Surjective r.hom.hom.left]
    (hr : B.hom ≫ r = q) :
    LinearKernelTower.IsCharacterLinearKernel D r
      (QuotientTerm.comparison A B (seriesHom_succ_le _ hN t)) := by
  let ρ := j ≫ GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k)
    (fun i => -(i.val : ℤ))
  have : Mono (seriesHom ρ t).hom.hom := (isRepresentedBy_seriesHom ρ t).1
  have : LocallyOfFiniteType (seriesScheme ρ t).X.hom :=
    locallyOfFiniteType_filtrationScheme ρ _ _
  have : IsAffineHom (seriesScheme ρ t).X.hom :=
    isAffineHom_filtrationScheme ρ _ _
  apply QuotientTerm.isCharacterLinearKernel_of_coordinate A B
    (seriesHom_succ_le ρ hN t) (isRepresentedBy_seriesHom ρ t)
    (isNormal_seriesHom j t) himage r (seriesCoordinate ρ hN t)
    (range_kernel_seriesCoordinate_comap ρ hN t) (seriesRatioCharacter d hN t)
  intro T g x
  have hr' : B.hom.hom.hom ≫ r.hom.hom = q.hom.hom :=
    congrArg (fun f => f.hom.hom) hr
  simpa only [Category.assoc, hr', seriesConjugation, filtrationConjugation, ρ,
    seriesHom] using
    seriesCoordinate_equivariant j q d hfac hN t g x

end Langlands.GroupScheme.TriangularLayer
