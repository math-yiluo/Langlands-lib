import Langlands.Representation.Jacquet.StandardCanonicalSectionStatement
import Langlands.Representation.Jacquet.StandardFixedVectorSubquotientGenerationStatement
import Langlands.Representation.Jacquet.StandardFixedVectorHeckeEquivalenceStatement

/-! # Renard VI.6.1 Proposition and VI.9.4 for compact open subgroups with an Iwahori
decomposition

Statements only, together with their comparison with the published versions. Renard 2026,
VI.6.1 (printed pp.176–177 / PDF pp.182–183), VI.6.3 Corollary (printed p.179 / PDF p.185)
and VI.9.4 (printed pp.200–201 / PDF pp.206–207). The source assumes of the compact open
subgroup `K` only an Iwahori decomposition, in the sense of V.5.2 (ii) (printed p.123 /
PDF p.129), along the standard parabolic considered (VI.6.1) or along every standard
parabolic (VI.6.3, VI.9.4). The published statements
`StandardCanonicalSectionStatement`, `StandardFixedVectorSubquotientGenerationStatement`
and `StandardFixedVectorHeckeEquivalenceStatement` assume the stronger
`StandardParabolicBasisMember` conditions. The statements below assume only the literal
ordered decomposition `HasIwahoriIntersectionDecomposition`; all other data and all
conclusions are unchanged.

* `StandardIwahoriCanonicalSectionStatement`: VI.6.1, (VI.6.1.2) and Proposition.
* `StandardIwahoriFixedVectorSubquotientGenerationStatement`: VI.9.4 Corollary (the
  VI.6.3 Corollary without admissibility).
* `StandardIwahoriFixedVectorHeckeEquivalenceStatement`: VI.9.4 Proposition.

Each implies the corresponding published statement (proved below), because the first
clause of `StandardParabolicBasisMember` is the Iwahori decomposition.
-/

noncomputable section

universe uF uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Jacquet

/-- Renard VI.6.1, (VI.6.1.2) and Proposition, for every compact open subgroup `K` with an
Iwahori decomposition `K = (K ∩ N̄(F)) (K ∩ M(F)) (K ∩ N(F))` along the actual standard
parabolic `P = MN`. For every admissible complex representation `V` there are `0 < ε ≤ 1`
and a section `s` of the Jacquet map `j : V^K → (V_N)^{K ∩ M}` such that, for every `t` in
the image of `C_A^+(ε)` (nonempty), `ker j = ker π(a_{t,K})`,
`V^K = ker π(a_{t,K}) ⊕ Im π(a_{t,K})`, `j` maps `Im π(a_{t,K})` bijectively onto
`(V_N)^{K ∩ M}`, and `s` is the inverse of this bijection, so that the decomposition and
the section do not depend on `t`. The data and conclusions are those of
`StandardCanonicalSectionStatement`; only the hypothesis on `K` is weakened. -/
def StandardIwahoriCanonicalSectionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : Smooth G.X.hom := hG.smooth
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    ∀ (S A : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
      (_hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
      (_hν : IsGenericCocharacter i ν) (J : Set (characterLattice S))
      (_hJ : J ⊆ simpleRelativeRoots i ν)
      (_hstandard : ∃ zeta, IsStandardCocharacter i ν J zeta)
      (q : A.toGrp ⟶ S.toGrp)
      (_hA : IsCompatibleStandardSplitComponent i ν J A q),
      let N := standardUnipotentPoints i ν J
      let M := standardLeviPoints i ν J
      ∀ (hMN : M ≤ Subgroup.normalizer N)
        (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
        (_hIwahori : HasIwahoriIntersectionDecomposition K.toSubgroup M N
          (standardOppositeUnipotentPoints i ν J))
        (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsAdmissible ρ),
        let j := fixedJacquetMap ρ N M hMN K.toSubgroup
        ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
          (∃ t : rationalPoints G, t ∈ standardComponentCAepsilon i ν J q ε) ∧
          ∃ s : fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype) →ₗ[ℂ]
              fixedVectors ρ K.toSubgroup,
            j.comp s = LinearMap.id ∧
            ∀ t ∈ standardComponentCAepsilon i ν J q ε,
              let C := compressedAction ρ hρ.1 K hK t
              LinearMap.ker j ≤ LinearMap.ker C ∧
              LinearMap.ker C = LinearMap.ker j ∧
              IsCompl (LinearMap.ker C) (LinearMap.range C) ∧
              Function.Bijective (compressedImageJacquetMap ρ hρ.1 K hK t N M hMN) ∧
              LinearMap.range C = stableImage ρ hρ.1 K hK t ∧
              powerKernelSup ρ hρ.1 K hK t = LinearMap.ker j ∧
              LinearMap.range s = LinearMap.range C ∧
              ∀ hb : Function.Bijective
                  (compressedImageJacquetMap ρ hρ.1 K hK t N M hMN),
                compressedImageLift ρ hρ.1 K hK t N M hMN hb = s

/-- Renard VI.9.4, Corollary, with the source's hypothesis on `K`: let `K` be a compact
open subgroup, contained and normal in `K₀` and with an Iwahori decomposition
`K = (K ∩ N̄_J(F)) (K ∩ M_J(F)) (K ∩ N_J(F))` along every standard parabolic `P_J`. If
`V^K` generates a smooth representation `V`, every subquotient of `V` is generated by its
`K`-fixed vectors. The compact subgroup `K₀` is given by its Iwasawa factorization
`G(F) = M_∅(F) N_∅(F) K₀`, as in `StandardFixedVectorSubquotientGenerationStatement`. -/
def StandardIwahoriFixedVectorSubquotientGenerationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : Smooth G.X.hom := hG.smooth
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
      (_hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
      (_hν : IsGenericCocharacter i ν)
      (_hstandard : ∀ J ⊆ simpleRelativeRoots i ν, ∃ zeta, IsStandardCocharacter i ν J zeta)
      (K₀ : Subgroup (rationalPoints G)) (_hK₀ : IsCompact (K₀ : Set (rationalPoints G)))
      (_hIwasawa : ∀ g : rationalPoints G, ∃ m ∈ standardLeviPoints i ν ∅,
        ∃ n ∈ standardUnipotentPoints i ν ∅, ∃ k ∈ K₀, g = m * n * k)
      (K : OpenSubgroup (rationalPoints G)) (_hK : IsCompact (K : Set (rationalPoints G)))
      (_hKK₀ : K.toSubgroup ≤ K₀) (_hnormal : K₀ ≤ Subgroup.normalizer K.toSubgroup)
      (_hIwahori : ∀ J ⊆ simpleRelativeRoots i ν,
        HasIwahoriIntersectionDecomposition K.toSubgroup (standardLeviPoints i ν J)
          (standardUnipotentPoints i ν J) (standardOppositeUnipotentPoints i ν J))
      (V : SmoothRep.{0, uF, uV} ℂ (rationalPoints G)),
      (∀ T : Subrepresentation V.representation,
          fixedVectors V.representation K.toSubgroup ≤ T.toSubmodule → T = ⊤) →
      ∀ D : SmoothRep.{0, uF, uV} ℂ (rationalPoints G), SmoothRep.IsSubquotient D V →
        ∀ T : Subrepresentation D.representation,
          fixedVectors D.representation K.toSubgroup ≤ T.toSubmodule → T = ⊤

/-- Renard VI.9.4, Proposition, with the source's hypothesis on `K` (as in
`StandardIwahoriFixedVectorSubquotientGenerationStatement`): the `K`-fixed-vector functor,
from the full subcategory of smooth representations generated by their `K`-fixed vectors
to modules over the Hecke algebra `ℂ[G(F)/K]^K` of `K`, is an equivalence. The Hecke
algebra is the measure-free `LevelHeckeAlgebra ℂ K` of
`StandardFixedVectorHeckeEquivalenceStatement`. -/
def StandardIwahoriFixedVectorHeckeEquivalenceStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : Smooth G.X.hom := hG.smooth
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
      (_hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
      (_hν : IsGenericCocharacter i ν)
      (_hstandard : ∀ J ⊆ simpleRelativeRoots i ν, ∃ zeta, IsStandardCocharacter i ν J zeta)
      (K₀ : Subgroup (rationalPoints G)) (_hK₀ : IsCompact (K₀ : Set (rationalPoints G)))
      (_hIwasawa : ∀ g : rationalPoints G, ∃ m ∈ standardLeviPoints i ν ∅,
        ∃ n ∈ standardUnipotentPoints i ν ∅, ∃ k ∈ K₀, g = m * n * k)
      (K : OpenSubgroup (rationalPoints G)) (_hK : IsCompact (K : Set (rationalPoints G)))
      (_hKK₀ : K.toSubgroup ≤ K₀) (_hnormal : K₀ ≤ Subgroup.normalizer K.toSubgroup)
      (_hIwahori : ∀ J ⊆ simpleRelativeRoots i ν,
        HasIwahoriIntersectionDecomposition K.toSubgroup (standardLeviPoints i ν J)
          (standardUnipotentPoints i ν J) (standardOppositeUnipotentPoints i ν J)),
      let P : ObjectProperty (SmoothRep.{0, uF, uV} ℂ (rationalPoints G)) := fun V =>
        ∀ T : Subrepresentation V.representation,
          fixedVectors V.representation K.toSubgroup ≤ T.toSubmodule → T = ⊤
      (P.ι ⋙ Langlands.Shimura.LevelHecke.heckeModuleFunctor ℂ K.toSubgroup).IsEquivalence

/-- The Iwahori-decomposition form of the VI.6.1 Proposition implies the published form
with the V.5.2 basis-member conditions. -/
theorem standardCanonicalSectionStatement_of_standardIwahori
    (h : StandardIwahoriCanonicalSectionStatement.{uF, uV}) :
    StandardCanonicalSectionStatement.{uF, uV} := by
  intro F _ _ _ _ G hG S A i hi ν hν J hJ hstandard q hA N M hMN K hK hBasis V _ _ ρ hρ
  exact h F G hG S A i hi ν hν J hJ hstandard q hA hMN K hK hBasis.1 V ρ hρ

/-- The Iwahori-decomposition form of the VI.9.4 Corollary implies the published form with
the V.5.2 basis-member conditions. -/
theorem standardFixedVectorSubquotientGenerationStatement_of_standardIwahori
    (h : StandardIwahoriFixedVectorSubquotientGenerationStatement.{uF, uV}) :
    StandardFixedVectorSubquotientGenerationStatement.{uF, uV} := by
  intro F _ _ _ _ G hG S i hi ν hν hstandard K₀ hK₀ hIwasawa K hK hKK₀ hnormal hBasis
  exact h F G hG S i hi ν hν hstandard K₀ hK₀ hIwasawa K hK hKK₀ hnormal
    (fun J hJ => (hBasis J hJ).choose_spec.choose_spec.2.1)

/-- The Iwahori-decomposition form of the VI.9.4 Proposition implies the published form
with the V.5.2 basis-member conditions. -/
theorem standardFixedVectorHeckeEquivalenceStatement_of_standardIwahori
    (h : StandardIwahoriFixedVectorHeckeEquivalenceStatement.{uF, uV}) :
    StandardFixedVectorHeckeEquivalenceStatement.{uF, uV} := by
  intro F _ _ _ _ G hG S i hi ν hν hstandard K₀ hK₀ hIwasawa K hK hKK₀ hnormal hBasis
  exact h F G hG S i hi ν hν hstandard K₀ hK₀ hIwasawa K hK hKK₀ hnormal
    (fun J hJ => (hBasis J hJ).choose_spec.choose_spec.2.1)

end Langlands.Jacquet
