import Langlands.GroupScheme.Rational.RealPointTopology
import Langlands.GroupScheme.Rational.OrthogonalOrbitDescent
import Langlands.GroupScheme.Rational.SteinbergCompatiblePinning
import Langlands.GroupScheme.Rational.SteinbergRationalGaloisTransport
import Langlands.GroupScheme.Lie.SplitRootWeightGaloisCoordinates
import Langlands.GroupScheme.Absolute.CocharacterDescentLattice
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Torus.WeylImageFinite
import Langlands.GroupScheme.Reductive.RootDatumGaloisCoroots
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.Geometry.Building.CocharacterUniformizer
import Langlands.GroupScheme.Rational.RelativeRootGroupAbsoluteGenerationProof
import Langlands.GroupScheme.Rational.NegativeRootPartnerGalois
import Langlands.GroupScheme.Rational.NormalizedRootExistenceProof
import Langlands.Algebra.RankOneRelationIdentities

/-! # Real identity-component values of conjugation-fixed simple coroots -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.GroupScheme.CocharacterUniformizer (cocharacterPoints)

namespace Langlands.GroupScheme.RealPointTopology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

local notation "b" => algebraBaseMap ℝ ℂ
local notation "complexTorus" T =>
  CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "complexHom" i =>
  CategoryTheory.Functor.map (GroupScheme.baseChange b) i

variable (G : GroupScheme (Spec (CommRingCat.of ℝ))) [IsAffine G.X.left]
  [IsAffineHom G.X.hom]

local instance realFixedSimpleCorootAlgClosure : IsAlgClosure ℝ ℂ :=
  ⟨inferInstance, Algebra.IsAlgebraic.of_finite ℝ ℂ⟩

local instance realFixedSimpleCorootAffineHom : IsAffineHom (baseChanged ℝ ℂ G).X.hom := by
  change IsAffineHom (Limits.pullback.snd G.X.hom b)
  infer_instance

/-- The two `ℝ`-automorphisms of `ℂ`. -/
theorem complexGalois_eq_one_or_conj (σ : ℂ ≃ₐ[ℝ] ℂ) : σ = 1 ∨ σ = Complex.conjAe := by
  rcases Complex.real_algHom_eq_id_or_conj σ.toAlgHom with h | h
  · left
    ext z
    exact congrArg (fun f : ℂ →ₐ[ℝ] ℂ => f z) h
  · right
    ext z
    exact congrArg (fun f : ℂ →ₐ[ℝ] ℂ => f z) h

/-- A Galois-fixed complex point of a root subgroup of a real torus is the extension of a
real point in the identity component, provided the root pairs nontrivially with a real
cocharacter of that torus. -/
theorem mem_map_identityComponentPreimage_of_fixed_rootSubgroup [Smooth G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of ℝ))} (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (β : characterLattice (complexTorus T))
    (hβ : latticePairing (complexTorus T) β (cocharacterLattice.baseChange b T ν) ≠ 0)
    {g : rationalPoints (baseChanged ℝ ℂ G)}
    (hg : ∀ σ : ℂ ≃ₐ[ℝ] ℂ, rationalConjugate ℝ ℂ G σ g = g)
    (hmem : g ∈ (RelativeRoot.subgroup (complexHom i) β).carrier (Over.mk (𝟙 _))) :
    g ∈ (identityComponentPreimage G).map (rationalExtend ℝ ℂ G) := by
  let S : CommGroupScheme (Spec (CommRingCat.of ℝ)) := Gm (Spec (CommRingCat.of ℝ))
  have hS : IsSplitTorus S.toGrp := isSplitTorus_gm
  let i' : S.toGrp ⟶ G := CommGroupScheme.groupHom ν ≫ i
  let gC : (complexTorus S) ⟶ (complexTorus T) := (CommGroupScheme.baseChange b).map ν
  let a' : characterLattice S := (characterLattice.baseChangeEquiv b S hS).symm (gC ≫ β)
  have ha' : characterLattice.baseChange b S a' = gC ≫ β :=
    (characterLattice.baseChangeEquiv b S hS).apply_symm_apply (gC ≫ β)
  have ha'0 : a' ≠ 0 := by
    intro h0
    apply hβ
    have hz : gC ≫ β = 0 := by rw [← ha', h0, map_zero]
    rw [latticePairing_apply]
    change gmEndEquiv ℂ (((Gm.commBaseChangeIso b).inv ≫ gC) ≫ β) = 0
    rw [Category.assoc, hz, Limits.comp_zero, map_zero]
  have hmem' : g ∈ Langlands.Geometry.Building.rootGroupPoints
      (S := complexTorus S) (complexHom i') (characterLattice.baseChange b S a') := by
    rw [ha']
    have h := RelativeRoot.subgroup_le_subgroup_comp_torusHom gC (complexHom i) β _ hmem
    have hi' : CommGroupScheme.groupHom gC ≫ (complexHom i) = complexHom i' := by
      simp only [i', Functor.map_comp]
      rfl
    rw [hi'] at h
    exact h
  obtain ⟨g₀, hg₀, rfl⟩ := exists_mem_rootGroupPoints_of_fixed ℝ ℂ i' hS a' ha'0 hg hmem'
  exact ⟨g₀, root_mem_connectedComponent_one G i' a' hg₀, rfl⟩

section Transport

variable {G}

/-- For a simple root whose character and pinning vector are fixed by `σ`, the normalized
root parametrization commutes with `σ` on rational points: `σ(x(c)) = x(σ c)`. -/
theorem rationalConjugate_rationalPoint_of_fixed
    (p : SplitPinning (baseChanged ℝ ℂ G))
    {T : CommGroupScheme (Spec (CommRingCat.of ℝ))} (i : T.toGrp ⟶ G)
    (eT : p.torus ≅ complexTorus T)
    (hT : p.inclusion = CommGroupScheme.groupHom eT.hom ≫ complexHom i)
    {a : p.base.support} (x : p.NormalizedRootParametrization a) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (hroot : characterLattice.congr eT (p.rootDatum.root a) =
      characterLattice.galoisRepresentation ℝ ℂ T σ
        (characterLattice.congr eT (p.rootDatum.root a)))
    (hvector : Lie.baseChangeGaloisEquiv ℝ ℂ G σ (p.pinning.rootVector a) =
      p.pinning.rootVector a)
    (c : ℂ) :
    rationalConjugate ℝ ℂ G σ (x.toRootParametrization.rationalPoint c) =
      x.toRootParametrization.rationalPoint (σ c) := by
  have hx := x.coefficientCurve_conjugate ℝ ℂ G σ i eT hT hroot hvector x
  apply (baseChangeCoeffEquiv ℝ ℂ G).injective
  rw [baseChangeCoeffEquiv_rationalConjugate]
  change Lie.affineMap G σ.toAlgHom _ = _
  rw [← x.coefficientCurve_evaluate_rationalPoint ℝ ℂ G,
    ← x.coefficientCurve_evaluate_rationalPoint ℝ ℂ G]
  let ev : MvPolynomial (Fin 1) ℂ →ₐ[ℝ] ℂ :=
    (MvPolynomial.aeval (fun _ : Fin 1 => c)).restrictScalars ℝ
  let evσ : MvPolynomial (Fin 1) ℂ →ₐ[ℝ] ℂ :=
    (MvPolynomial.aeval (fun _ : Fin 1 => σ c)).restrictScalars ℝ
  change Lie.affineMap G σ.toAlgHom (Lie.affineMap G ev _) = Lie.affineMap G evσ _
  calc
    _ = Lie.affineMap G (σ.toAlgHom.comp ev) (x.coefficientCurve ℝ ℂ G) :=
      (Lie.affineMap_comp G ev σ.toAlgHom _).symm
    _ = Lie.affineMap G (evσ.comp (PolynomialGalois.lineConjugate ℝ ℂ σ))
        (x.coefficientCurve ℝ ℂ G) :=
      congrArg (fun f => Lie.affineMap G f (x.coefficientCurve ℝ ℂ G))
        (PolynomialGalois.aeval_comp_conjugate ℝ ℂ σ c).symm
    _ = Lie.affineMap G evσ (Lie.affineMap G
        (PolynomialGalois.lineConjugate ℝ ℂ σ) (x.coefficientCurve ℝ ℂ G)) :=
      Lie.affineMap_comp G _ evσ _
    _ = _ := congrArg (Lie.affineMap G evσ) hx

/-- Under the same hypotheses, the negative partner also commutes with `σ`:
`σ(y(d)) = y(σ d)`. -/
theorem rationalConjugate_negPoint_of_fixed
    (p : SplitPinning (baseChanged ℝ ℂ G))
    {T : CommGroupScheme (Spec (CommRingCat.of ℝ))} (i : T.toGrp ⟶ G)
    (eT : p.torus ≅ complexTorus T)
    (hT : p.inclusion = CommGroupScheme.groupHom eT.hom ≫ complexHom i)
    {a : p.base.support} (x : p.NormalizedRootParametrization a) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (hroot : characterLattice.congr eT (p.rootDatum.root a) =
      characterLattice.galoisRepresentation ℝ ℂ T σ
        (characterLattice.congr eT (p.rootDatum.root a)))
    (hvector : Lie.baseChangeGaloisEquiv ℝ ℂ G σ (p.pinning.rootVector a) =
      p.pinning.rootVector a)
    (d : ℂ) :
    rationalConjugate ℝ ℂ G σ (x.negPoint d) = x.negPoint (σ d) :=
  SplitPinning.NormalizedRootParametrization.negPoint_rationalConjugate ℝ ℂ i p eT hT x x σ
    hroot (rationalConjugate_rationalPoint_of_fixed p i eT hT x σ hroot hvector) d

/-- Under the same hypotheses, the positive point of the chosen linked parametrization
commutes with `σ`: `σ(x₊(c)) = x₊(σ c)`. -/
theorem rationalConjugate_xpPoint_of_fixed
    (p : SplitPinning (baseChanged ℝ ℂ G))
    {T : CommGroupScheme (Spec (CommRingCat.of ℝ))} (i : T.toGrp ⟶ G)
    (eT : p.torus ≅ complexTorus T)
    (hT : p.inclusion = CommGroupScheme.groupHom eT.hom ≫ complexHom i)
    {a : p.base.support} (x : p.NormalizedRootParametrization a) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (hroot : characterLattice.congr eT (p.rootDatum.root a) =
      characterLattice.galoisRepresentation ℝ ℂ T σ
        (characterLattice.congr eT (p.rootDatum.root a)))
    (hvector : Lie.baseChangeGaloisEquiv ℝ ℂ G σ (p.pinning.rootVector a) =
      p.pinning.rootVector a)
    (c : ℂ) :
    rationalConjugate ℝ ℂ G σ (x.linked.xpPoint c) = x.linked.xpPoint (σ c) := by
  rw [x.xpPoint_linked, x.xpPoint_linked]
  exact rationalConjugate_rationalPoint_of_fixed p i eT hT x σ hroot hvector c

end Transport

section Generic

variable {k : Type} [Field k] {H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom] {p : SplitPinning H} {a : p.base.support}

/-- The positive point of the chosen linked parametrization lies in the root subgroup. -/
theorem linked_xpPoint_mem (x : p.NormalizedRootParametrization a) (c : k) :
    x.linked.xpPoint c ∈
      (RelativeRoot.subgroup p.inclusion (p.rootDatum.root a)).carrier (Over.mk (𝟙 _)) := by
  rw [x.xpPoint_linked]
  exact x.toRootParametrization.rationalPoint_mem c

/-- The torus element of the rank-one relation data of the chosen linked parametrization is
the image of the coroot point of the pinned torus. -/
theorem rankOneData_h_eq_map (x : p.NormalizedRootParametrization a) (t : kˣ) :
    (x.linked.rankOneData
        (SplitPinning.NormalizedRootParametrization.pairing_root_coroot (a := a))).h t =
      rationalPoints.map p.inclusion (cocharacterPoints k p.torus (p.rootDatum.coroot a) t) :=
  rfl

end Generic

section Pinning

attribute [local instance] rootsGaloisAction

variable {G}

omit [IsAffineHom G.X.hom] in
/-- Each root of a reduced root datum of the complexified maximal torus is an actual root. -/
theorem root_mem_roots_complex {T : CommGroupScheme (Spec (CommRingCat.of ℝ))}
    {i : T.toGrp ⟶ G} {J : Type}
    {P : RootDatum J (characterLattice (complexTorus T)) (cocharacterLattice (complexTorus T))}
    (hP : IsRootDatumOf (T := complexTorus T) (complexHom i) P) (a : J) :
    P.root a ∈ roots (T := complexTorus T) (G := baseChanged ℝ ℂ G) (complexHom i) := by
  rw [← hP.2.1]
  exact ⟨a, rfl⟩

/-- The split pinning of `G_ℂ` given by a real maximal torus that splits over `ℂ`, a reduced
root datum, a base, and the stabilizer-equivariant coordinates on the root lines. -/
def complexFixedPinning [Smooth G.X.hom] (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of ℝ))} (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hsplit : IsSplitTorus (complexTorus T).toGrp)
    {J : Type} [Finite J]
    (P : RootDatum J (characterLattice (complexTorus T)) (cocharacterLattice (complexTorus T)))
    [hred : P.IsReduced] (hP : IsRootDatumOf (T := complexTorus T) (complexHom i) P)
    (B : P.Base) : SplitPinning (baseChanged ℝ ℂ G) where
  isConnectedReductive := connectedReductiveFieldExtensionStatement ℝ ℂ G hG
  torus := complexTorus T
  inclusion := complexHom i
  isSplitTorus := hsplit
  isMaximalTorus := (maximalTorusBaseChange ℝ ℂ G T i hi.1 hi.2.1).mp hi
  rootIndex := J
  rootDatum := P
  isRootDatum := hP
  isReduced := hred
  base := B
  pinning := ⟨fun a => splitRootWeightEquivariantLinearEquiv ℝ ℂ i hG hi hsplit
    ⟨P.root a, root_mem_roots_complex hP a⟩⟩


/-- The pinning vector of `complexFixedPinning` is the chosen equivariant coordinate at `1`. -/
theorem complexFixedPinning_rootVector [Smooth G.X.hom] (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of ℝ))} (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hsplit : IsSplitTorus (complexTorus T).toGrp)
    {J : Type} [Finite J]
    (P : RootDatum J (characterLattice (complexTorus T)) (cocharacterLattice (complexTorus T)))
    [P.IsReduced] (hP : IsRootDatumOf (T := complexTorus T) (complexHom i) P)
    (B : P.Base) (a : B.support) :
    (complexFixedPinning hG i hi hsplit P hP B).pinning.rootVector a =
      (splitRootWeightEquivariantLinearEquiv ℝ ℂ i hG hi hsplit
        ⟨P.root a, root_mem_roots_complex hP a⟩ 1).val := rfl

/-- The equivariant coordinate vector of a root fixed by `σ` is fixed by `σ`. -/
theorem splitRootVector_galois (k L : Type) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj H).X.hom]
    (j : T.toGrp ⟶ H) (hH : IsConnectedReductive H) (hj : IsMaximalTorus j)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    (β : roots (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj H)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j))
    (σ : L ≃ₐ[k] L)
    (hσ : characterLattice.galoisRepresentation k L T σ β.val = β.val) :
    Lie.baseChangeGaloisEquiv k L H σ
        (splitRootWeightEquivariantLinearEquiv k L j hH hj hT β 1).val =
      (splitRootWeightEquivariantLinearEquiv k L j hH hj hT β 1).val := by
  have h0 := splitRootWeightEquivariantLinearEquiv_galois k L j hH hj hT β
    ⟨σ, MulAction.mem_stabilizer_iff.mpr (Subtype.ext hσ)⟩ 1
  have h1 : σ (1 : L) = 1 := map_one σ
  exact h0.trans (congrArg
    (fun z => (splitRootWeightEquivariantLinearEquiv k L j hH hj hT β z).val) h1)

/-- The pinning vector of a root fixed by `σ` is fixed by the semilinear Lie action of `σ`. -/
theorem complexFixedPinning_rootVector_galois [Smooth G.X.hom] (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of ℝ))} (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hsplit : IsSplitTorus (complexTorus T).toGrp)
    {J : Type} [Finite J]
    (P : RootDatum J (characterLattice (complexTorus T)) (cocharacterLattice (complexTorus T)))
    [P.IsReduced] (hP : IsRootDatumOf (T := complexTorus T) (complexHom i) P)
    (B : P.Base) (a : B.support) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (hσ : characterLattice.galoisRepresentation ℝ ℂ T σ (P.root a) = P.root a) :
    Lie.baseChangeGaloisEquiv ℝ ℂ G σ
        ((complexFixedPinning hG i hi hsplit P hP B).pinning.rootVector a) =
      (complexFixedPinning hG i hi hsplit P hP B).pinning.rootVector a := by
  rw [complexFixedPinning_rootVector]
  exact splitRootVector_galois ℝ ℂ i hG hi hsplit _ σ hσ

end Pinning

section Main

variable {G}

/-- The coroot of an index fixed by `σ` is fixed by the Galois action of `σ`. The two
instance hypotheses of the Library comparison are taken as explicit arguments. -/
theorem galoisRepresentation_coroot_eq_of_fixed (k E : Type) [Field k] [Field E] [Algebra k E]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj H).X.hom]
    (i : T.toGrp ⟶ H)
    (hmono : Mono ((GroupScheme.baseChange (algebraBaseMap k E)).map i).hom.hom.left)
    (hfin : Finite (weylImage (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map i)))
    {J : Type}
    {P : RootDatum J (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))
      (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))}
    (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map i) P)
    {σ : E ≃ₐ[k] E} {j : J} (hj : IsRootDatumOf.galoisRootIndexEquiv k E i hP σ j = j) :
    cocharacterLattice.galoisRepresentation k E T σ (P.coroot j) = P.coroot j :=
  (IsRootDatumOf.galoisRootIndexEquiv_coroot k E i hP σ j).symm.trans (congrArg P.coroot hj)

/-- The character of `complexFixedPinning` at a simple root, transported along the identity. -/
theorem complexFixedPinning_hroot [Smooth G.X.hom] (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of ℝ))} (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hsplit : IsSplitTorus (complexTorus T).toGrp)
    {J : Type} [Finite J]
    (P : RootDatum J (characterLattice (complexTorus T)) (cocharacterLattice (complexTorus T)))
    [P.IsReduced] (hP : IsRootDatumOf (T := complexTorus T) (complexHom i) P)
    (B : P.Base) (a : B.support) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (hσ : characterLattice.galoisRepresentation ℝ ℂ T σ (P.root a) = P.root a) :
    characterLattice.congr (Iso.refl (complexTorus T))
        ((complexFixedPinning hG i hi hsplit P hP B).rootDatum.root (a : J)) =
      characterLattice.galoisRepresentation ℝ ℂ T σ
        (characterLattice.congr (Iso.refl (complexTorus T))
          ((complexFixedPinning hG i hi hsplit P hP B).rootDatum.root (a : J))) := by
  have hc : characterLattice.congr (Iso.refl (complexTorus T)) (P.root a) = P.root a := by
    rw [characterLattice.congr_apply, Iso.refl_inv, Category.id_comp]
  exact hc.trans (hσ.symm.trans (congrArg _ hc.symm))

/-- The inclusion of `complexFixedPinning` is the complexified inclusion. -/
theorem complexFixedPinning_inclusion [Smooth G.X.hom] (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of ℝ))} (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hsplit : IsSplitTorus (complexTorus T).toGrp)
    {J : Type} [Finite J]
    (P : RootDatum J (characterLattice (complexTorus T)) (cocharacterLattice (complexTorus T)))
    [P.IsReduced] (hP : IsRootDatumOf (T := complexTorus T) (complexHom i) P)
    (B : P.Base) :
    (complexFixedPinning hG i hi hsplit P hP B).inclusion =
      CommGroupScheme.groupHom (Iso.refl (complexTorus T)).hom ≫ complexHom i :=
  rfl

/-- A real coefficient of the normalized parametrization of a conjugation-fixed simple root
gives a point extended from the real identity component. -/
theorem complexFixedPinning_xpPoint_mem [Smooth G.X.hom] (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of ℝ))} (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hsplit : IsSplitTorus (complexTorus T).toGrp)
    {J : Type} [Finite J]
    (P : RootDatum J (characterLattice (complexTorus T)) (cocharacterLattice (complexTorus T)))
    [P.IsReduced] (hP : IsRootDatumOf (T := complexTorus T) (complexHom i) P)
    (B : P.Base) (a : B.support)
    (hσ : ∀ σ : ℂ ≃ₐ[ℝ] ℂ,
      characterLattice.galoisRepresentation ℝ ℂ T σ (P.root a) = P.root a)
    (ν : cocharacterLattice T)
    (hν : latticePairing (complexTorus T) (P.root a) (cocharacterLattice.baseChange b T ν) ≠ 0)
    (x : (complexFixedPinning hG i hi hsplit P hP B).NormalizedRootParametrization a)
    (r : ℝ) (c : ℂ) (hc : algebraMap ℝ ℂ r = c) :
    x.linked.xpPoint c ∈ (identityComponentPreimage G).map (rationalExtend ℝ ℂ G) := by
  subst hc
  refine mem_map_identityComponentPreimage_of_fixed_rootSubgroup G i ν (P.root a) hν
    (fun σ => ?_) (linked_xpPoint_mem x _)
  exact (rationalConjugate_xpPoint_of_fixed (complexFixedPinning hG i hi hsplit P hP B) i
    (Iso.refl _) (complexFixedPinning_inclusion hG i hi hsplit P hP B) x σ
    (complexFixedPinning_hroot hG i hi hsplit P hP B a σ (hσ σ))
    (complexFixedPinning_rootVector_galois hG i hi hsplit P hP B a σ (hσ σ)) _).trans
    (congrArg _ (σ.commutes r))

/-- A real coefficient of the negative partner of a conjugation-fixed simple root gives a
point extended from the real identity component. -/
theorem complexFixedPinning_negPoint_mem [Smooth G.X.hom] (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of ℝ))} (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hsplit : IsSplitTorus (complexTorus T).toGrp)
    {J : Type} [Finite J]
    (P : RootDatum J (characterLattice (complexTorus T)) (cocharacterLattice (complexTorus T)))
    [P.IsReduced] (hP : IsRootDatumOf (T := complexTorus T) (complexHom i) P)
    (B : P.Base) (a : B.support)
    (hσ : ∀ σ : ℂ ≃ₐ[ℝ] ℂ,
      characterLattice.galoisRepresentation ℝ ℂ T σ (P.root a) = P.root a)
    (ν : cocharacterLattice T)
    (hν : latticePairing (complexTorus T) (P.root a) (cocharacterLattice.baseChange b T ν) ≠ 0)
    (x : (complexFixedPinning hG i hi hsplit P hP B).NormalizedRootParametrization a)
    (r : ℝ) (c : ℂ) (hc : algebraMap ℝ ℂ r = c) :
    x.negPoint c ∈ (identityComponentPreimage G).map (rationalExtend ℝ ℂ G) := by
  subst hc
  have hν' : latticePairing (complexTorus T) (-P.root a)
      (cocharacterLattice.baseChange b T ν) ≠ 0 := by
    rw [map_neg, LinearMap.neg_apply, neg_ne_zero]
    exact hν
  refine mem_map_identityComponentPreimage_of_fixed_rootSubgroup G i ν (-P.root a) hν'
    (fun σ => ?_) (x.negPoint_mem _)
  exact (rationalConjugate_negPoint_of_fixed (complexFixedPinning hG i hi hsplit P hP B) i
    (Iso.refl _) (complexFixedPinning_inclusion hG i hi hsplit P hP B) x σ
    (complexFixedPinning_hroot hG i hi hsplit P hP B a σ (hσ σ))
    (complexFixedPinning_rootVector_galois hG i hi hsplit P hP B a σ (hσ σ)) _).trans
    (congrArg _ (σ.commutes r))

/-- The torus element `h(u)` of the rank-one relation data at a real unit `u`, written
through the rank-one relation as a word in real root points, lies in the image of the real
identity component. -/
theorem complexFixedPinning_rankOne_h_mem [Smooth G.X.hom] (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of ℝ))} (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hsplit : IsSplitTorus (complexTorus T).toGrp)
    {J : Type} [Finite J]
    (P : RootDatum J (characterLattice (complexTorus T)) (cocharacterLattice (complexTorus T)))
    [P.IsReduced] (hP : IsRootDatumOf (T := complexTorus T) (complexHom i) P)
    (B : P.Base) (a : B.support)
    (hσ : ∀ σ : ℂ ≃ₐ[ℝ] ℂ,
      characterLattice.galoisRepresentation ℝ ℂ T σ (P.root a) = P.root a)
    (ν : cocharacterLattice T)
    (hν : latticePairing (complexTorus T) (P.root a) (cocharacterLattice.baseChange b T ν) ≠ 0)
    (x : (complexFixedPinning hG i hi hsplit P hP B).NormalizedRootParametrization a)
    (u : ℂˣ) (r : ℝ) (hu : (u : ℂ) = algebraMap ℝ ℂ r) :
    (x.linked.rankOneData
        (SplitPinning.NormalizedRootParametrization.pairing_root_coroot
          (p := complexFixedPinning hG i hi hsplit P hP B) (a := a))).h u ∈
      (identityComponentPreimage G).map (rationalExtend ℝ ℂ G) := by
  rw [Langlands.Algebra.RankOneRelation.Data.h_eq_word]
  refine mul_mem (mul_mem (mul_mem (inv_mem ?_) ?_) ?_) (inv_mem ?_)
  · exact complexFixedPinning_negPoint_mem hG i hi hsplit P hP B a hσ ν hν x (r⁻¹ * (r - 1)) _
      (by rw [hu, map_mul, map_inv₀, map_sub, map_one])
  · exact complexFixedPinning_xpPoint_mem hG i hi hsplit P hP B a hσ ν hν x 1 _ (map_one _)
  · exact complexFixedPinning_negPoint_mem hG i hi hsplit P hP B a hσ ν hν x (r - 1) _
      (by rw [hu, map_sub, map_one])
  · exact complexFixedPinning_xpPoint_mem hG i hi hsplit P hP B a hσ ν hν x r⁻¹ _
      (by rw [hu, map_inv₀])

/-- The value of the coroot of a conjugation-fixed simple root at a real unit lies in the
image of the real identity component. -/
theorem complexFixedPinning_coroot_mem [Smooth G.X.hom] (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of ℝ))} (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hsplit : IsSplitTorus (complexTorus T).toGrp)
    {J : Type} [Finite J]
    (P : RootDatum J (characterLattice (complexTorus T)) (cocharacterLattice (complexTorus T)))
    [P.IsReduced] (hP : IsRootDatumOf (T := complexTorus T) (complexHom i) P)
    (B : P.Base) (a : B.support)
    (hσ : ∀ σ : ℂ ≃ₐ[ℝ] ℂ,
      characterLattice.galoisRepresentation ℝ ℂ T σ (P.root a) = P.root a)
    (ν : cocharacterLattice T)
    (hν : latticePairing (complexTorus T) (P.root a) (cocharacterLattice.baseChange b T ν) ≠ 0)
    (x : (complexFixedPinning hG i hi hsplit P hP B).NormalizedRootParametrization a)
    (u : ℂˣ) (r : ℝ) (hu : (u : ℂ) = algebraMap ℝ ℂ r) :
    rationalPoints.map (complexHom i)
        (cocharacterPoints ℂ (complexTorus T) (P.coroot a) u) ∈
      (identityComponentPreimage G).map (rationalExtend ℝ ℂ G) := by
  have key : rationalPoints.map (complexHom i)
      (cocharacterPoints ℂ (complexTorus T) (P.coroot a) u) =
      (x.linked.rankOneData
        (SplitPinning.NormalizedRootParametrization.pairing_root_coroot
          (p := complexFixedPinning hG i hi hsplit P hP B) (a := a))).h u :=
    (rankOneData_h_eq_map x u).symm
  rw [key]
  exact complexFixedPinning_rankOne_h_mem hG i hi hsplit P hP B a hσ ν hν x u r hu

/-- Over `ℝ`, an index fixed by complex conjugation is fixed by every element of the Galois
group of `ℂ / ℝ`. -/
theorem complexGaloisRootIndexEquiv_eq {T : CommGroupScheme (Spec (CommRingCat.of ℝ))}
    (i : T.toGrp ⟶ G) {J : Type}
    {P : RootDatum J (characterLattice (complexTorus T)) (cocharacterLattice (complexTorus T))}
    (hP : IsRootDatumOf (T := complexTorus T) (complexHom i) P) {j : J}
    (hfix : IsRootDatumOf.galoisRootIndexEquiv ℝ ℂ i hP Complex.conjAe j = j)
    (σ : ℂ ≃ₐ[ℝ] ℂ) : IsRootDatumOf.galoisRootIndexEquiv ℝ ℂ i hP σ j = j := by
  rcases complexGalois_eq_one_or_conj σ with rfl | rfl
  · exact DFunLike.congr_fun ((IsRootDatumOf.galoisRootIndexAction ℝ ℂ i hP).map_one) j
  · exact hfix

/-- For a real maximal torus splitting over `ℂ` and a simple root whose character and coroot
are fixed by the Galois group, the value of the coroot at a real unit is the extension of a
point of `G(ℝ)⁰`. -/
theorem fixedSimpleCoroot_mem_of_fixed (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of ℝ))} (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hsplit : IsSplitTorus (complexTorus T).toGrp)
    {J : Type} [Finite J]
    (P : RootDatum J (characterLattice (complexTorus T)) (cocharacterLattice (complexTorus T)))
    [P.IsReduced] (hP : IsRootDatumOf (T := complexTorus T) (complexHom i) P)
    (B : P.Base) {j : J} (hj : j ∈ B.support)
    (hroot : ∀ σ : ℂ ≃ₐ[ℝ] ℂ,
      characterLattice.galoisRepresentation ℝ ℂ T σ (P.root j) = P.root j)
    (hcoroot : ∀ σ : ℂ ≃ₐ[ℝ] ℂ,
      cocharacterLattice.galoisRepresentation ℝ ℂ T σ (P.coroot j) = P.coroot j)
    (u : ℂˣ) (r : ℝ) (hu : (u : ℂ) = algebraMap ℝ ℂ r) :
    rationalPoints.map (complexHom i)
        (cocharacterPoints ℂ (complexTorus T) (P.coroot j) u) ∈
      (identityComponentPreimage G).map (rationalExtend ℝ ℂ G) := by
  have : Smooth G.X.hom := hG.smooth
  have : IsClosedImmersion i.hom.hom.left := hi.2.1
  have : IsAffine T.X.left := isAffine_of_isAffineHom i.hom.hom.left
  have hν : cocharacterLattice.baseChange b T
      (cocharacterLattice.descend ℝ ℂ T (P.coroot j) hcoroot) = P.coroot j :=
    cocharacterLattice.baseChange_descend ℝ ℂ T _ hcoroot
  have h2 : latticePairing (complexTorus T) (P.root j) (P.coroot j) = 2 := by
    rw [← hP.1]
    exact P.root_coroot_two j
  have hpair : latticePairing (complexTorus T) (P.root j) (cocharacterLattice.baseChange b T
      (cocharacterLattice.descend ℝ ℂ T (P.coroot j) hcoroot)) ≠ 0 := by
    rw [hν, h2]
    norm_num
  exact complexFixedPinning_coroot_mem hG i hi hsplit P hP B ⟨j, hj⟩ hroot _ hpair
    (Classical.choice
      ((complexFixedPinning hG i hi hsplit P hP B).nonempty_normalizedRootParametrization ⟨j, hj⟩))
    u r hu

/-- Over `ℝ`, the root of an index fixed by complex conjugation is Galois-fixed. -/
theorem complexGalois_root_eq {T : CommGroupScheme (Spec (CommRingCat.of ℝ))}
    (i : T.toGrp ⟶ G) {J : Type}
    {P : RootDatum J (characterLattice (complexTorus T)) (cocharacterLattice (complexTorus T))}
    (hP : IsRootDatumOf (T := complexTorus T) (complexHom i) P) {j : J}
    (hfix : IsRootDatumOf.galoisRootIndexEquiv ℝ ℂ i hP Complex.conjAe j = j)
    (σ : ℂ ≃ₐ[ℝ] ℂ) :
    characterLattice.galoisRepresentation ℝ ℂ T σ (P.root j) = P.root j :=
  (IsRootDatumOf.galoisRootIndexEquiv_root ℝ ℂ i hP σ j).symm.trans
    (congrArg P.root (complexGaloisRootIndexEquiv_eq i hP hfix σ))

/-- Over `ℝ`, the coroot of an index fixed by complex conjugation is Galois-fixed. -/
theorem complexGalois_coroot_eq {T : CommGroupScheme (Spec (CommRingCat.of ℝ))}
    (i : T.toGrp ⟶ G) (hmono : Mono (complexHom i).hom.hom.left)
    (hfin : Finite (weylImage (T := complexTorus T) (complexHom i))) {J : Type}
    {P : RootDatum J (characterLattice (complexTorus T)) (cocharacterLattice (complexTorus T))}
    (hP : IsRootDatumOf (T := complexTorus T) (complexHom i) P) {j : J}
    (hfix : IsRootDatumOf.galoisRootIndexEquiv ℝ ℂ i hP Complex.conjAe j = j)
    (σ : ℂ ≃ₐ[ℝ] ℂ) :
    cocharacterLattice.galoisRepresentation ℝ ℂ T σ (P.coroot j) = P.coroot j :=
  galoisRepresentation_coroot_eq_of_fixed ℝ ℂ i hmono hfin hP
    (complexGaloisRootIndexEquiv_eq i hP hfix σ)

/-- The value at `-1` of a simple coroot with Galois-fixed root and coroot lies in the image
of `G(ℝ)⁰`. -/
theorem fixedSimpleCoroot_neg_one_mem_of_fixed (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of ℝ))} (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hsplit : IsSplitTorus (complexTorus T).toGrp)
    {J : Type} [Finite J]
    (P : RootDatum J (characterLattice (complexTorus T)) (cocharacterLattice (complexTorus T)))
    [P.IsReduced] (hP : IsRootDatumOf (T := complexTorus T) (complexHom i) P)
    (B : P.Base) {j : J} (hj : j ∈ B.support)
    (hroot : ∀ σ : ℂ ≃ₐ[ℝ] ℂ,
      characterLattice.galoisRepresentation ℝ ℂ T σ (P.root j) = P.root j)
    (hcoroot : ∀ σ : ℂ ≃ₐ[ℝ] ℂ,
      cocharacterLattice.galoisRepresentation ℝ ℂ T σ (P.coroot j) = P.coroot j) :
    rationalPoints.map (complexHom i)
        (cocharacterPoints ℂ (complexTorus T) (P.coroot j) (-1)) ∈
      (identityComponentPreimage G).map (rationalExtend ℝ ℂ G) := by
  refine fixedSimpleCoroot_mem_of_fixed hG i hi hsplit P hP B hj hroot hcoroot _ (-1) ?_
  rw [Units.val_neg, Units.val_one, map_neg, map_one]

/-- **Main theorem.** For a real maximal torus splitting over `ℂ` and a conjugation-fixed
simple root, the complex point `α^∨(-1)` is the extension of a point of `G(ℝ)⁰`. -/
theorem fixedSimpleCoroot_neg_one_mem (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of ℝ))} (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hsplit : IsSplitTorus (complexTorus T).toGrp)
    {J : Type} [Finite J]
    (P : RootDatum J (characterLattice (complexTorus T)) (cocharacterLattice (complexTorus T)))
    [P.IsReduced] (hP : IsRootDatumOf (T := complexTorus T) (complexHom i) P)
    (B : P.Base) {j : J} (hj : j ∈ B.support)
    (hfix : IsRootDatumOf.galoisRootIndexEquiv ℝ ℂ i hP Complex.conjAe j = j) :
    rationalPoints.map (complexHom i)
        (cocharacterPoints ℂ (complexTorus T) (P.coroot j) (-1)) ∈
      (identityComponentPreimage G).map (rationalExtend ℝ ℂ G) := by
  have : Smooth G.X.hom := hG.smooth
  have : Smooth (baseChanged ℝ ℂ G).X.hom :=
    (connectedReductiveFieldExtensionStatement ℝ ℂ G hG).smooth
  have hmaxC : IsMaximalTorus (T := complexTorus T) (complexHom i) :=
    (maximalTorusBaseChange ℝ ℂ G T i hi.1 hi.2.1).mp hi
  exact fixedSimpleCoroot_neg_one_mem_of_fixed hG i hi hsplit P hP B hj
    (complexGalois_root_eq i hP hfix)
    (complexGalois_coroot_eq i hmaxC.2.1.mono
      (splitTorusWeylImageFinite ℂ (baseChanged ℝ ℂ G) (complexTorus T) hsplit (complexHom i)
        hmaxC.2.1) hP hfix)

set_option linter.defProp false in
variable (G) in
/-- **Fixed simple coroot signs.** For a connected reductive real group `G`, every real
maximal torus `T` whose complexification splits, every reduced root datum of `T_ℂ` in `G_ℂ`,
every base and every simple index `j` fixed by the index permutation of complex conjugation,
the complex point `α_j^∨(-1)` of `G_ℂ` is the scalar extension of a real point in the
identity component of `G(ℝ)`. -/
def fixedSimpleCorootSignsInIdentity_of_isConnectedReductive (hG : IsConnectedReductive G) :
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of ℝ))) (i : T.toGrp ⟶ G),
      IsMaximalTorus i → IsSplitTorus (complexTorus T).toGrp →
      ∀ (J : Type) [Finite J]
        (P : RootDatum J (characterLattice (complexTorus T))
          (cocharacterLattice (complexTorus T)))
        [P.IsReduced] (hP : IsRootDatumOf (T := complexTorus T) (complexHom i) P)
        (B : P.Base) (j : J), j ∈ B.support →
        IsRootDatumOf.galoisRootIndexEquiv ℝ ℂ i hP Complex.conjAe j = j →
        rationalPoints.map (complexHom i)
            (cocharacterPoints ℂ (complexTorus T) (P.coroot j) (-1)) ∈
          (identityComponentPreimage G).map (rationalExtend ℝ ℂ G) :=
  fun _ i hi hsplit _ _ P _ hP B _ hj hfix =>
    fixedSimpleCoroot_neg_one_mem hG i hi hsplit P hP B hj hfix

end Main

end Langlands.GroupScheme.RealPointTopology
