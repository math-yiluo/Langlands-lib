import Langlands.GroupScheme.MatrixRepresentation.IrreducibleRestriction
import Langlands.GroupScheme.Reductive.GaloisTwistWeights
import Langlands.GroupScheme.MatrixRepresentation.TitsAlgebraFixed
import Langlands.GroupScheme.MatrixRepresentation.StableProjection

/-! # Tits algebras under restriction along isomorphisms defined over `k` -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

section Ext

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} {n : Type} [Fintype n] [DecidableEq n]

/-- A matrix representation is determined by its matrices on all points. -/
theorem ext_pointMatrix {ρ₁ ρ₂ : MatrixRepresentation G n}
    (h : ∀ (T : Over (Spec R)) (x : T ⟶ G.X), ρ₁.pointMatrix T x = ρ₂.pointMatrix T x) :
    ρ₁ = ρ₂ := by
  have h1 := h G.X (𝟙 _)
  rw [pointMatrix_apply, pointMatrix_apply, Category.id_comp, Category.id_comp] at h1
  apply Grp.hom_ext
  exact (GeneralLinear.pointsEquiv n R G.X).injective h1

end Ext

section Transport

variable {B : Scheme.{u}} {R : CommRingCat.{u}} (b : Spec R ⟶ B) (a : Spec R ⟶ Spec R)
  (ha : a ≫ b = b) {G H : GroupScheme B} {n : Type} [Fintype n] [DecidableEq n]

/-- Transport along `a` commutes with restriction along a homomorphism over the base. -/
theorem transport_restrict (ρ : MatrixRepresentation ((GroupScheme.baseChange b).obj G) n)
    (f : H ⟶ G) :
    transport b a ha H (ρ.restrict ((GroupScheme.baseChange b).map f)) =
      (transport b a ha G ρ).restrict ((GroupScheme.baseChange b).map f) := by
  apply ext_pointMatrix
  intro T x
  rw [pointMatrix_transport, pointMatrix_transport_restrict]

end Transport

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Galois twists commute with restriction along homomorphisms defined over `k`. -/
theorem galoisTwist_restrict (σ : K ≃ₐ[k] K)
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (f : H ⟶ G) :
    galoisTwist σ (ρ.restrict ((GroupScheme.baseChange (algebraBaseMap k K)).map f)) =
      (galoisTwist σ ρ).restrict ((GroupScheme.baseChange (algebraBaseMap k K)).map f) :=
  transport_restrict _ _ _ ρ f

/-- Galois intertwiners restrict along homomorphisms defined over `k`. -/
theorem intertwines_restrict_galoisTwist (σ : K ≃ₐ[k] K)
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n}
    {P : Matrix n n K} (hP : ρ.Intertwines (galoisTwist σ ρ) P) (f : H ⟶ G) :
    (ρ.restrict ((GroupScheme.baseChange (algebraBaseMap k K)).map f)).Intertwines
      (galoisTwist σ (ρ.restrict ((GroupScheme.baseChange (algebraBaseMap k K)).map f))) P := by
  rw [galoisTwist_restrict]
  exact hP.restrict _

variable [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- Restriction along an isomorphism preserves scalarity of self-intertwiners. -/
theorem scalar_of_restrict_iso {F : Type u} [Field F]
    {G' H' : GroupScheme (Spec (CommRingCat.of F))} {ρ : MatrixRepresentation G' n}
    (hscalar : ∀ C : Matrix n n F, ρ.Intertwines ρ C → ∃ c : F, C = Matrix.scalar n c)
    (e : H' ≅ G') :
    ∀ C : Matrix n n F, (ρ.restrict e.hom).Intertwines (ρ.restrict e.hom) C →
      ∃ c : F, C = Matrix.scalar n c := by
  intro C hC
  apply hscalar
  have h := hC.restrict e.inv
  simpa only [restrict_comp, e.inv_hom_id, restrict_id] using h


/-- The Tits algebra is unchanged by restriction along an isomorphism defined over `k`. -/
theorem titsAlgebra_restrict_iso [IsGalois k K] [Nonempty n]
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (hirr : ρ.IsIrreducible)
    (hscalar : ∀ C : Matrix n n K, ρ.Intertwines ρ C → ∃ c : K, C = Matrix.scalar n c)
    (P : (K ≃ₐ[k] K) → Matrix n n K) (hPunit : ∀ σ, IsUnit (P σ))
    (hP : ∀ σ, ρ.Intertwines (galoisTwist σ ρ) (P σ)) (e : H ≅ G) :
    titsAlgebra (ρ.restrict ((GroupScheme.baseChange (algebraBaseMap k K)).map e.hom)) =
      titsAlgebra ρ := by
  rw [titsAlgebra_eq_twistedFixed ρ hirr hscalar P hPunit hP]
  exact titsAlgebra_eq_twistedFixed _ (hirr.restrict_iso ((GroupScheme.baseChange
      (algebraBaseMap k K)).mapIso e)) (scalar_of_restrict_iso hscalar
      ((GroupScheme.baseChange (algebraBaseMap k K)).mapIso e)) P hPunit
      (fun σ => intertwines_restrict_galoisTwist σ (hP σ) e.hom)

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme

open MatrixRepresentation

/-- The Tits algebra of an irreducible representation of `G_K` with scalar self-intertwiners and
Galois intertwiners is unchanged by restriction along the scalar extension of an isomorphism
`H ≅ G` defined over `k`. -/
def TitsAlgebraRestrictIsoStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (G H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (n : Type) [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n),
    ρ.IsIrreducible →
    (∀ C : Matrix n n K, ρ.Intertwines ρ C → ∃ c : K, C = Matrix.scalar n c) →
    ∀ (P : (K ≃ₐ[k] K) → Matrix n n K), (∀ σ, IsUnit (P σ)) →
      (∀ σ, ρ.Intertwines (galoisTwist σ ρ) (P σ)) →
      ∀ e : H ≅ G,
        titsAlgebra (ρ.restrict ((GroupScheme.baseChange (algebraBaseMap k K)).map e.hom)) =
          titsAlgebra ρ

theorem titsAlgebraRestrictIso : TitsAlgebraRestrictIsoStatement.{u} := by
  intro k K _ _ _ _ G H _ _ n _ _ _ ρ hirr hscalar P hPu hP e
  exact titsAlgebra_restrict_iso ρ hirr hscalar P hPu hP e

end Langlands.GroupScheme
