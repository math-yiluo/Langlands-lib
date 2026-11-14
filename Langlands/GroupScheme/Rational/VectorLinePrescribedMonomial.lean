import Langlands.GroupScheme.Rational.MonicRootParametrization
import Langlands.GroupScheme.Rational.VectorLineEquivariantMap
import Langlands.GroupScheme.Rational.VectorLineMonomialTests
import Langlands.GroupScheme.MatrixRepresentation.TorusEquivariantAdditive
import Langlands.GroupScheme.Rational.SteinbergRootMapUniqueness

/-! # Prescribed degrees for actual equivariant vector-line maps -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.RelativeRoot.VectorLine

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {V W : GroupScheme (Spec (CommRingCat.of k))}
    (e : ∀ U : Over (Spec (CommRingCat.of k)),
      (U ⟶ V.X) ≃* Multiplicative (Fin 1 → Γ(U.left, ⊤)))
    (d : ∀ U : Over (Spec (CommRingCat.of k)),
      (U ⟶ W.X) ≃* Multiplicative (Fin 1 → Γ(U.left, ⊤)))
    (p : V ⟶ W)
    {a : AutomorphicAction T.toGrp V} {b : AutomorphicAction T.toGrp W}
    {α β : characterLattice T}
    (he : IsWeightVectorCoordinates a α e) (hd : IsWeightVectorCoordinates b β d)
    (hp : ∀ (U : Over (Spec (CommRingCat.of k))) (t : U ⟶ T.X) (x : U ⟶ V.X),
      a.act t x ≫ p.hom.hom = b.act t (x ≫ p.hom.hom))
    [IsAffineHom T.toGrp.X.hom] [IsAffineHom V.X.hom] [Epi p.hom.hom]
    (hT : IsSplitTorus T.toGrp) (hα : α ≠ 0)

/-- The nonzero scalar in the monomial of an actual epimorphic equivariant
map between naturally coordinated lines. -/
def monomialScalar : kˣ :=
  (powerMonomial e d p he hd hp hT hα).scalar

include he hd hp

/-- A prescribed integral character equation identifies the monomial degree. -/
theorem polynomial_eq_monomialScalar (n : ℕ) (hβ : β = n • α) :
    polynomial e d p = C (monomialScalar e d p he hd hp hT hα : k) * X ^ n := by
  let M := powerMonomial e d p he hd hp hT hα
  have hαrat : Langlands.LinearAlgebra.RationalSpan.toRat α ≠ 0 := by
    intro hz
    apply hα
    apply hT.character_toRat_injective
    simpa using hz
  have hdeg : ringExpChar k ^ M.exponent = n := by
    apply Nat.cast_injective (R := ℚ)
    have h := congrArg Langlands.LinearAlgebra.RationalSpan.toRat
      (M.character_eq.symm.trans hβ)
    simp only [map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ] at h
    exact smul_left_injective ℚ hαrat h
  simpa only [monomialScalar, M, hdeg] using M.polynomial_eq

/-- The scalar is fixed over the original field before any test scheme is chosen. -/
theorem coordinate_eq_monomialScalar (n : ℕ) (hβ : β = n • α)
    (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ V.X) :
    (d U (x ≫ p.hom.hom)).toAdd 0 =
      U.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv
        (monomialScalar e d p he hd hp hT hα : k)) * (e U x).toAdd 0 ^ n := by
  apply coordinate_monomial_of_affine e d p he.1 hd.1
  intro A xA
  rw [← polynomial_aeval e d p he.1 hd.1 xA,
    polynomial_eq_monomialScalar e d p he hd hp hT hα n hβ]
  simp

end Langlands.GroupScheme.RelativeRoot.VectorLine

namespace Langlands.GroupScheme.VectorGroup

variable {k : Type u} [Field k]
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}

local notation "R" => CommRingCat.of k
local notation "V" => groupScheme R 1
local notation "coords" => coordinates R 1

/-- An epimorphic equivariant additive map with a prescribed weight ratio is
one nonzero scalar monomial on every scheme test. -/
theorem exists_scalarPoint_comp_of_weightEquivariant
    (hT : IsSplitTorus T.toGrp) {α β : characterLattice T} (hα : α ≠ 0)
    (p : V ⟶ V) [Epi p.hom.hom]
    (hp : ∀ (U : Over (Spec R)) (t : U ⟶ T.X) (x : U ⟶ (V).X),
      (weightAction α).act t x ≫ p.hom.hom =
        (weightAction β).act t (x ≫ p.hom.hom))
    (n : ℕ) (hβ : β = n • α) :
    ∃ c : kˣ, ∀ (U : Over (Spec R)) (a : Γ(U.left, ⊤)),
      scalarPoint R U a ≫ p.hom.hom =
        scalarPoint R U (U.hom.appTop ((Scheme.ΓSpecIso R).inv (c : k)) * a ^ n) := by
  let : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  let : IsAffineHom (V).X.hom :=
    RelativeRoot.IsVectorGroupOfDimension.isAffineHom
      ⟨coords, isNaturalVectorCoordinates⟩
  let he := isWeightVectorCoordinates_weightAction (n := 1) α
  let hd := isWeightVectorCoordinates_weightAction (n := 1) β
  let c := RelativeRoot.VectorLine.monomialScalar coords coords p he hd hp hT hα
  refine ⟨c, ?_⟩
  intro U a
  have hm := RelativeRoot.VectorLine.coordinate_eq_monomialScalar
    coords coords p he hd hp hT hα n hβ U (scalarPoint R U a)
  rw [coordinates_scalarPoint] at hm
  apply points_ext
  intro j
  rw [coordinates_scalarPoint, Subsingleton.elim j 0]
  exact hm

/-- Pullback of a character agrees with restriction of its actual scalar action. -/
theorem weightAction_pullback_act (t : T ⟶ T') (β : characterLattice T')
    (U : Over (Spec R)) (s : U ⟶ T.X) (v : U ⟶ (V).X) :
    (weightAction (t ≫ β)).act s v =
      (weightAction β).act (s ≫ t.hom.hom) v := by
  apply points_ext
  intro j
  rw [coordinates_weightAction_act, coordinates_weightAction_act]
  congr 1

/-- A restriction square through a monic target representative inherits
full-torus equivariance from the two supplied ambient conjugation laws. -/
theorem IsTorusEquivariant.restriction_equivariant
    {G G' : GroupScheme (Spec R)} {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'}
    {x : V ⟶ G} {x' : V ⟶ G'} {α : characterLattice T} {β : characterLattice T'}
    (hx : IsTorusEquivariant i x α) (hx' : IsTorusEquivariant i' x' β)
    (φ : G ⟶ G') (t : T ⟶ T')
    (hsq : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    (p : V ⟶ V) (hp : p ≫ x' = x ≫ φ) [Mono x'.hom.hom]
    (U : Over (Spec R)) (s : U ⟶ T.X) (v : U ⟶ (V).X) :
    (weightAction α).act s v ≫ p.hom.hom =
      (weightAction (t ≫ β)).act s (v ≫ p.hom.hom) := by
  have hpoint (w : U ⟶ (V).X) :
      (w ≫ p.hom.hom) ≫ x'.hom.hom = (w ≫ x.hom.hom) ≫ φ.hom.hom := by
    rw [Category.assoc, ← Grp.comp_hom_hom, hp, Grp.comp_hom_hom, Category.assoc]
  have htorus : (s ≫ i.hom.hom) ≫ φ.hom.hom =
      (s ≫ t.hom.hom) ≫ i'.hom.hom := by
    rw [Category.assoc, ← Grp.comp_hom_hom, hsq, Grp.comp_hom_hom, Category.assoc]
    rfl
  apply (cancel_mono x'.hom.hom).mp
  rw [hpoint, hx.weightAction_comp, AutomorphicAction.conjugation_act,
    MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, htorus,
    weightAction_pullback_act, hx'.weightAction_comp,
    AutomorphicAction.conjugation_act, hpoint]

/-- The one field scalar computes the ambient map in arbitrary supplied
equivariant parametrizations of its source and target lines. -/
theorem IsTorusEquivariant.exists_scalarPoint_comp_of_restriction
    {G G' : GroupScheme (Spec R)} {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'}
    {x : V ⟶ G} {x' : V ⟶ G'} {α : characterLattice T} {β : characterLattice T'}
    (hx : IsTorusEquivariant i x α) (hx' : IsTorusEquivariant i' x' β)
    (hT : IsSplitTorus T.toGrp) (hα : α ≠ 0)
    (φ : G ⟶ G') (t : T ⟶ T')
    (hsq : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    (p : V ⟶ V) (hp : p ≫ x' = x ≫ φ) [Mono x'.hom.hom] [Epi p.hom.hom]
    (n : ℕ) (hβ : t ≫ β = n • α) :
    ∃ c : kˣ, ∀ (U : Over (Spec R)) (a : Γ(U.left, ⊤)),
      scalarPoint R U a ≫ x.hom.hom ≫ φ.hom.hom =
        scalarPoint R U (U.hom.appTop ((Scheme.ΓSpecIso R).inv (c : k)) * a ^ n) ≫
          x'.hom.hom := by
  obtain ⟨c, hc⟩ := exists_scalarPoint_comp_of_weightEquivariant hT hα p
    (hx.restriction_equivariant hx' φ t hsq p hp) n hβ
  refine ⟨c, fun U a => ?_⟩
  calc
    _ = (scalarPoint R U a ≫ p.hom.hom) ≫ x'.hom.hom := by
      have h := congrArg (fun q : V ⟶ G' => scalarPoint R U a ≫ q.hom.hom) hp
      simpa only [Grp.comp_hom_hom, Category.assoc] using h.symm
    _ = _ := congrArg (· ≫ x'.hom.hom) (hc U a)

end Langlands.GroupScheme.VectorGroup
