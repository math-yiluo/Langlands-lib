import Langlands.GroupScheme.Dynamic.UnipotentSolvable
import Langlands.GroupScheme.CorepresentedClosedSubgroup
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Closed embeddings of dynamic identity-limit groups into unitriangular groups -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Reindex the rows and columns of an invertible matrix. -/
def matrixReindex (a : n ≃ m) (A : Type u) [CommRing A] : GL n A ≃* GL m A :=
  Units.mapEquiv (Matrix.reindexAlgEquiv A A a).toMulEquiv

theorem matrixReindex_map (a : n ≃ m) {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (f : A →+* B) (g : GL n A) :
    matrixReindex a B (Matrix.GeneralLinearGroup.map f g) =
      Matrix.GeneralLinearGroup.map f (matrixReindex a A g) := by
  apply Units.ext
  rfl

variable (a : n ≃ m) (R : CommRingCat.{u})

/-- Matrix reindexing on points of the actual general linear group schemes. -/
def reindexPoints (T : Over (Spec R)) :
    (T ⟶ (groupScheme n R).X) ≃* (T ⟶ (groupScheme m R).X) :=
  (pointsEquiv n R T).trans
    ((matrixReindex a Γ(T.left, ⊤)).trans (pointsEquiv m R T).symm)

theorem pointsEquiv_reindexPoints (T : Over (Spec R))
    (x : T ⟶ (groupScheme n R).X) :
    pointsEquiv m R T (reindexPoints a R T x) =
      matrixReindex a Γ(T.left, ⊤) (pointsEquiv n R T x) :=
  (pointsEquiv m R T).apply_symm_apply _

theorem reindexPoints_naturality {T T' : Over (Spec R)} (b : T' ⟶ T)
    (x : T ⟶ (groupScheme n R).X) :
    reindexPoints a R T' (b ≫ x) = b ≫ reindexPoints a R T x := by
  apply (pointsEquiv m R T').injective
  rw [pointsEquiv_reindexPoints, pointsEquiv_naturality,
    pointsEquiv_naturality, pointsEquiv_reindexPoints, matrixReindex_map]

/-- The isomorphism of actual general linear group schemes induced by an index equivalence. -/
def reindexIso : groupScheme n R ≅ groupScheme m R :=
  isoOfPoints (reindexPoints a R) (reindexPoints_naturality a R)

theorem pointsEquiv_reindexIso (T : Over (Spec R))
    (x : T ⟶ (groupScheme n R).X) :
    pointsEquiv m R T (x ≫ (reindexIso a R).hom.hom.hom) =
      matrixReindex a Γ(T.left, ⊤) (pointsEquiv n R T x) := by
  rw [reindexIso, comp_isoOfPoints_hom, pointsEquiv_reindexPoints]

/-- Sorting weights in decreasing order carries a block identity-limit matrix into the
standard upper unitriangular subgroup, including its diagonal equations. -/
theorem matrixReindex_mem_unitriangular (A : Type u) [CommRing A] (e : n → ℤ)
    (g : GL n A) (hg : g ∈ blockUnipotentSubgroup A e) :
    matrixReindex (antitoneEnumeration e).symm A g ∈
      blockUnipotentSubgroup A (fun i : Fin (Fintype.card n) => -(i.val : ℤ)) := by
  intro i j hij
  have hji : j ≤ i := by
    change -(i.val : ℤ) ≤ -(j.val : ℤ) at hij
    omega
  change (g : Matrix n n A) (antitoneEnumeration e i) (antitoneEnumeration e j) = _
  rw [hg _ _ (antitone_antitoneEnumeration e hji)]
  simp only [Matrix.one_apply, (antitoneEnumeration e).injective.eq_iff]

end Langlands.GroupScheme.GeneralLinear

namespace Langlands.GroupScheme.Dynamic

open Langlands.GroupScheme.GeneralLinear

section SuppliedDiagonalization

variable {R : CommRingCat.{u}} {G U : GroupScheme (Spec R)}
  {n : Type} [Fintype n] [DecidableEq n]
  (χ : (Gm (Spec R)).toGrp ⟶ G) (j : U ⟶ G)
  (hU : (unipotent χ).IsRepresentedBy j)
  (ρ : G ⟶ groupScheme n R) (e : n → ℤ)
  (hχ : χ ≫ ρ = diagonalCocharacter n R e)

include χ hU hχ

/-- A diagonalizing matrix representation, followed by decreasing weight order, sends
the represented identity-limit group into the concrete upper unitriangular subgroup. -/
theorem unitriangularAmbient_range_le :
    SubgroupFunctor.range
      (j ≫ ρ ≫ (reindexIso (antitoneEnumeration e).symm R).hom) ≤
        blockUnipotent (Fin (Fintype.card n)) R (fun i => -(i.val : ℤ)) := by
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have hy : y ≫ j.hom.hom ∈ (unipotent χ).carrier T := by
    rw [← hU.2]
    exact ⟨y, rfl⟩
  have hρy := unipotent_le_comap χ ρ T hy
  change (y ≫ j.hom.hom) ≫ ρ.hom.hom ∈ (unipotent (χ ≫ ρ)).carrier T at hρy
  rw [hχ, unipotent_diagonalCocharacter] at hρy
  change pointsEquiv (Fin (Fintype.card n)) R T
    (y ≫ (j ≫ ρ ≫ (reindexIso (antitoneEnumeration e).symm R).hom).hom.hom) ∈
      blockUnipotentSubgroup Γ(T.left, ⊤) (fun i : Fin (Fintype.card n) => -(i.val : ℤ))
  simp only [Grp.comp_hom_hom, ← Category.assoc]
  rw [pointsEquiv_reindexIso]
  exact matrixReindex_mem_unitriangular Γ(T.left, ⊤) e _ hρy

/-- The actual factorization of a dynamic identity-limit representative into the standard
upper unitriangular scheme, for a supplied diagonalizing representation. -/
def unitriangularFactor :
    U ⟶ blockUnipotentScheme (Fin (Fintype.card n)) R (fun i => -(i.val : ℤ)) :=
  (isRepresentedBy_blockUnipotent (Fin (Fintype.card n)) R (fun i => -(i.val : ℤ))).factorHom
    (j ≫ ρ ≫ (reindexIso (antitoneEnumeration e).symm R).hom)
    (unitriangularAmbient_range_le χ j hU ρ e hχ)

theorem unitriangularFactor_comp :
    unitriangularFactor χ j hU ρ e hχ ≫
      blockUnipotentHom (Fin (Fintype.card n)) R (fun i => -(i.val : ℤ)) =
        j ≫ ρ ≫ (reindexIso (antitoneEnumeration e).symm R).hom :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

/-- Closedness in the original group and a faithful closed matrix representation imply
closedness of the constructed unitriangular factor. -/
theorem isClosedSubgroup_unitriangularFactor (hj : IsClosedSubgroup j)
    (hρ : IsClosedSubgroup ρ) :
    IsClosedSubgroup (unitriangularFactor χ j hU ρ e hχ) := by
  apply IsClosedSubgroup.of_comp
    (isClosedSubgroup_blockUnipotentHom (Fin (Fintype.card n)) R (fun i => -(i.val : ℤ)))
  rw [unitriangularFactor_comp]
  exact hj.comp (hρ.comp_iso (reindexIso (antitoneEnumeration e).symm R))

end SuppliedDiagonalization

section Field

variable {k : Type u} [Field k]
  {G U : GroupScheme (Spec (CommRingCat.of k))}

/-- Every closed representative of the dynamic identity-limit subgroup of an affine
locally finite-type group over a field admits a closed embedding into a standard
upper unitriangular group scheme. -/
theorem exists_closed_unitriangularEmbedding
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (j : U ⟶ G)
    (hU : (unipotent χ).IsRepresentedBy j) (hj : IsClosedSubgroup j) :
    ∃ (N : ℕ) (f : U ⟶ blockUnipotentScheme (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ))), IsClosedSubgroup f := by
  classical
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  obtain ⟨g, e, hge⟩ := exists_matrix_innerIso_comp_eq_diagonalCocharacter (χ ≫ ρ)
  let c := innerIso (groupScheme (Fin N) (CommRingCat.of k))
    (baseOfMatrix (CommRingCat.of k) g)
  have hdiag : χ ≫ (ρ ≫ c.hom) = diagonalCocharacter (Fin N) (CommRingCat.of k) e := by
    simpa only [Category.assoc] using hge
  exact ⟨Fintype.card (Fin N), unitriangularFactor χ j hU (ρ ≫ c.hom) e hdiag,
    isClosedSubgroup_unitriangularFactor χ j hU (ρ ≫ c.hom) e hdiag hj (hρ.comp_iso c)⟩

end Field

end Langlands.GroupScheme.Dynamic
