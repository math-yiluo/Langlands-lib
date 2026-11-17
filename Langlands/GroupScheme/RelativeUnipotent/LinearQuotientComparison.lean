import Langlands.GroupScheme.FppfQuotientUniqueness
import Langlands.GroupScheme.VectorWeightLinearity
import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.Dynamic.UnipotentCocharacterConjugacy
import Langlands.GroupScheme.Rational.TorusActionBridge

/-! # Linear comparisons between compatible common-weight vector quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.FppfQuotientComparison

variable {S : Scheme.{u}} {G G' K K' Q Q' H : GroupScheme S}

/-- Pulling a full fppf quotient back through a source isomorphism preserves its
actual kernel, transported as a subgroup functor on all tests. -/
theorem precomp_iso {F : SubgroupFunctor G'} {q : G' ⟶ Q}
    (hq : RelativeRoot.IsFppfQuotient F q) (e : G ≅ G') :
    RelativeRoot.IsFppfQuotient (F.comap e.hom) (e.hom ≫ q) := by
  have : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget S).mapIso ((Grp.forget _).mapIso e)).hom)
  have := hq.1
  have := hq.2.1
  have := hq.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Flat (e.hom.hom.hom.left ≫ q.hom.hom.left)
    infer_instance
  · change Surjective (e.hom.hom.hom.left ≫ q.hom.hom.left)
    infer_instance
  · change LocallyOfFinitePresentation (e.hom.hom.hom.left ≫ q.hom.hom.left)
    infer_instance
  · ext T x
    rw [mem_range_kernelι_iff, SubgroupFunctor.mem_comap, ← hq.2.2.2,
      mem_range_kernelι_iff, Grp.comp_hom_hom, ← Category.assoc]

/-- Compatible actual isomorphisms of two consecutive terms identify their
represented kernel ranges. -/
theorem range_comap_of_compatible_isos (i : K ⟶ G) (i' : K' ⟶ G')
    (e : G ≅ G') (eK : K ≅ K') (he : i ≫ e.hom = eK.hom ≫ i') :
    (SubgroupFunctor.range i').comap e.hom = SubgroupFunctor.range i := by
  have hs : i.hom.hom ≫ e.hom.hom.hom = eK.hom.hom.hom ≫ i'.hom.hom :=
    congrArg (fun f => f.hom.hom) he
  ext T x
  rw [SubgroupFunctor.mem_comap, SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y ≫ eK.inv.hom.hom, ?_⟩
    apply (isoPointsEquiv e T).injective
    change ((y ≫ eK.inv.hom.hom) ≫ i.hom.hom) ≫ e.hom.hom.hom = x ≫ e.hom.hom.hom
    calc
      _ = y ≫ eK.inv.hom.hom ≫ (i.hom.hom ≫ e.hom.hom.hom) := by
        simp only [Category.assoc]
      _ = y ≫ eK.inv.hom.hom ≫ (eK.hom.hom.hom ≫ i'.hom.hom) := by rw [hs]
      _ = y ≫ i'.hom.hom := by
        rw [← Category.assoc eK.inv.hom.hom eK.hom.hom.hom,
          iso_inv_hom_hom, Category.id_comp]
      _ = x ≫ e.hom.hom.hom := hy
  · rintro ⟨y, rfl⟩
    refine ⟨y ≫ eK.hom.hom.hom, ?_⟩
    simp only [Category.assoc]
    rw [← hs]

/-- The canonical actual quotient isomorphism induced by compatible consecutive-term
isomorphisms. -/
def isoOfCompatibleTerms (i : K ⟶ G) (i' : K' ⟶ G')
    {q : G ⟶ Q} {q' : G' ⟶ Q'}
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hq' : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i') q')
    (e : G ≅ G') (eK : K ≅ K') (he : i ≫ e.hom = eK.hom ≫ i') : Q ≅ Q' :=
  fppfIso hq (by
    have h := precomp_iso hq' e
    rw [range_comap_of_compatible_isos i i' e eK he] at h
    exact h)

@[reassoc]
theorem isoOfCompatibleTerms_fac (i : K ⟶ G) (i' : K' ⟶ G')
    {q : G ⟶ Q} {q' : G' ⟶ Q'}
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hq' : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i') q')
    (e : G ≅ G') (eK : K ≅ K') (he : i ≫ e.hom = eK.hom ≫ i') :
    q ≫ (isoOfCompatibleTerms i i' hq hq' e eK he).hom = e.hom ≫ q' :=
  fppfIso_fac hq _

/-- An equivariant comparison of sources induces an equivariant comparison of
actual quotients. Quotient points need only lift after a flat surjective refinement. -/
theorem isEquivariant_of_fac {q : G ⟶ Q} {q' : G' ⟶ Q'} {F : SubgroupFunctor G}
    [QuasiCompact q.hom.hom.left]
    (hq : RelativeRoot.IsFppfQuotient F q)
    (a : AutomorphicAction H G) (a' : AutomorphicAction H G')
    (b : AutomorphicAction H Q) (b' : AutomorphicAction H Q')
    (ha : a.IsEquivariant b q) (ha' : a'.IsEquivariant b' q')
    (e : G ⟶ G') (he : a.IsEquivariant a' e)
    (E : Q ⟶ Q') (hE : q ≫ E = e ≫ q') : b.IsEquivariant b' E := by
  have := hq.1
  have := hq.2.1
  have hf : q.hom.hom ≫ E.hom.hom = e.hom.hom ≫ q'.hom.hom :=
    congrArg (fun f => f.hom.hom) hE
  intro T h x
  apply AutomorphicAction.hom_ext_of_local_quotient_lift q x
  intro V p g hpg
  calc
    p ≫ (b.act h x ≫ E.hom.hom) =
        b.act (p ≫ h) (p ≫ x) ≫ E.hom.hom := by
      rw [← Category.assoc, b.naturality]
    _ = (a.act (p ≫ h) g ≫ q.hom.hom) ≫ E.hom.hom := by rw [hpg, ← ha]
    _ = (a.act (p ≫ h) g ≫ e.hom.hom) ≫ q'.hom.hom := by
      rw [Category.assoc, hf, ← Category.assoc]
    _ = a'.act (p ≫ h) (g ≫ e.hom.hom) ≫ q'.hom.hom := by rw [he]
    _ = b'.act (p ≫ h) ((g ≫ e.hom.hom) ≫ q'.hom.hom) := ha' _ _
    _ = p ≫ b'.act h (x ≫ E.hom.hom) := by
      rw [b'.naturality, ← Category.assoc, hpg]
      simp only [Category.assoc]
      rw [hf]

end Langlands.GroupScheme.FppfQuotientComparison

namespace Langlands.GroupScheme.VectorGroup

open AffineLine Corepresented.UnipotentPrimitive

variable {R : CommRingCat.{u}} {n m : ℕ}

/-- The positive-power character action used on an exact-weight quotient. -/
abbrev powerWeightAction (n : ℕ) (d : ℕ) :
    AutomorphicAction (Gm (Spec R)).toGrp (groupScheme R n) :=
  weightAction (Gm.powerHom (Spec R) (d : ℤ))

theorem charValue_power_unitPoint (d : ℕ) (A : CommAlgCat.{u} R) (t : Aˣ) :
    (Corepresented.affineSectionsIso A).hom.hom.toRingHom
      (charValue (Gm.powerHom (Spec R) (d : ℤ))
        ((algSpec R).obj (op A))
        (unitPoint (S := Spec R) ((algSpec R).obj (op A)).hom t)) =
      (t : A) ^ d := by
  rw [Corepresented.affineSectionsIso_hom_ringHom]
  change (Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom
    (unitPoint (S := Spec R) ((algSpec R).obj (op A)).hom t ≫
      (CommGroupScheme.groupHom (Gm.powerHom (Spec R) (d : ℤ))).hom.hom)).val = _
  rw [Gm.powerHom_apply, Gm.comp_zsmul_id, map_zpow, Corepresented.affinePointsEquiv_unitPoint]
  simp

theorem affinePointsEquiv_powerWeightAction (d : ℕ) (A : CommAlgCat.{u} R) (t : Aˣ)
    (x : (algSpec R).obj (op A) ⟶ (groupScheme R n).X) :
    Multiplicative.toAdd (α := Fin n → A)
      (Corepresented.affinePointsEquiv (functor R n) (corepresentableBy R n) A
        ((powerWeightAction n d).act
          (unitPoint (S := Spec R) ((algSpec R).obj (op A)).hom t) x)) =
      (t : A) ^ d • Multiplicative.toAdd (α := Fin n → A)
        (Corepresented.affinePointsEquiv (functor R n) (corepresentableBy R n) A x) := by
  rw [← Corepresented.map_affineSectionsIso_pointsEquiv (functor R n)
      (corepresentableBy R n) A ((powerWeightAction n d).act
        (unitPoint (S := Spec R) ((algSpec R).obj (op A)).hom t) x),
    ← Corepresented.map_affineSectionsIso_pointsEquiv (functor R n)
      (corepresentableBy R n) A x]
  change (fun j => (Corepresented.affineSectionsIso A).hom.hom
    ((coordinates R n _ ((powerWeightAction n d).act _ x)).toAdd j)) = _
  rw [coordinates_weightAction_act]
  funext j
  change (Corepresented.affineSectionsIso A).hom.hom.toRingHom (_ * _) = _
  rw [map_mul, charValue_power_unitPoint]
  rfl

/-- Actual equivariance for the common rank-one power character supplies precisely
the all-algebra scalar premise required by arbitrary-ring vector linearity. -/
theorem hasScalarWeight_of_equivariant (φ : groupScheme R n ⟶ groupScheme R m)
    (d : ℕ)
    (hφ : (powerWeightAction n d).IsEquivariant (powerWeightAction m d) φ) :
    HasScalarWeight (pointTransformation φ) d := by
  intro A t x
  let P := Corepresented.affinePointsEquiv (functor R n) (corepresentableBy R n) A
  let Q := Corepresented.affinePointsEquiv (functor R m) (corepresentableBy R m) A
  let s : (algSpec R).obj (op A) ⟶ (Gm (Spec R)).X :=
    unitPoint (S := Spec R) ((algSpec R).obj (op A)).hom t
  let v := P.symm (Multiplicative.ofAdd x)
  have hs : P.symm (Multiplicative.ofAdd ((t : A) ^ d • x)) =
      (powerWeightAction n d).act s v := by
    apply P.injective
    apply (Multiplicative.toAdd (α := Fin n → A)).injective
    dsimp only [P, s]
    rw [MulEquiv.apply_symm_apply, affinePointsEquiv_powerWeightAction]
    change (t : A) ^ d • x = (t : A) ^ d • Multiplicative.toAdd (α := Fin n → A)
      (P (P.symm (Multiplicative.ofAdd x)))
    rw [MulEquiv.apply_symm_apply]
    rfl
  have h := congrArg (fun z => Multiplicative.toAdd (α := Fin m → A) (Q z)) (hφ s v)
  dsimp only [Q, s] at h
  rw [affinePointsEquiv_powerWeightAction] at h
  change Multiplicative.toAdd (α := Fin m → A)
      (Q (P.symm (Multiplicative.ofAdd ((t : A) ^ d • x)) ≫ φ.hom.hom)) =
    (t : A) ^ d • Multiplicative.toAdd (α := Fin m → A)
      (Q (P.symm (Multiplicative.ofAdd x) ≫ φ.hom.hom))
  rw [hs]
  exact h

end Langlands.GroupScheme.VectorGroup

namespace Langlands.GroupScheme.FppfQuotientComparison

open VectorGroup

variable {R : CommRingCat.{u}}
  {G G' K K' : GroupScheme (Spec R)} {n m : ℕ}
  (i : K ⟶ G) (i' : K' ⟶ G')
  {q : G ⟶ groupScheme R n} {q' : G' ⟶ groupScheme R m}
  (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
  (hq' : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i') q')
  (e : G ≅ G') (eK : K ≅ K') (hs : i ≫ e.hom = eK.hom ≫ i')
  [hqcompact : QuasiCompact q.hom.hom.left]
  (a : AutomorphicAction (Gm (Spec R)).toGrp G)
  (a' : AutomorphicAction (Gm (Spec R)).toGrp G') (d : ℕ)
  (ha : a.IsEquivariant (powerWeightAction n d) q)
  (ha' : a'.IsEquivariant (powerWeightAction m d) q')
  (he : a.IsEquivariant a' e.hom)

include a a' ha ha' he hqcompact

/-- The canonically induced quotient isomorphism has the actual common scalar weight,
deduced from equivariance of the term isomorphism and both quotient maps. -/
theorem isoOfCompatibleTerms_hasScalarWeight :
    HasScalarWeight (pointTransformation (isoOfCompatibleTerms i i' hq hq' e eK hs).hom) d :=
  hasScalarWeight_of_equivariant _ d
    (isEquivariant_of_fac hq a a' (powerWeightAction n d) (powerWeightAction m d)
      ha ha' e.hom he _ (isoOfCompatibleTerms_fac i i' hq hq' e eK hs))

/-- Compatible equivariant consecutive-term isomorphisms induce actual linear
equivalences on vector quotients over every coefficient algebra. -/
def linearEquivOfCompatibleTerms (hd : 0 < d) (A : CommAlgCat.{u} R) :
    (Fin n → A) ≃ₗ[A] (Fin m → A) :=
  linearEquivOfWeight (isoOfCompatibleTerms i i' hq hq' e eK hs) hd
    (isoOfCompatibleTerms_hasScalarWeight i i' hq hq' e eK hs a a' d ha ha' he) A

@[simp]
theorem linearEquivOfCompatibleTerms_apply (hd : 0 < d) (A : CommAlgCat.{u} R)
    (x : Fin n → A) :
    linearEquivOfCompatibleTerms i i' hq hq' e eK hs a a' d ha ha' he hd A x =
      additiveApp (pointTransformation (isoOfCompatibleTerms i i' hq hq' e eK hs).hom) A x :=
  rfl

/-- The induced actual quotient map is one base-ring matrix homomorphism. -/
theorem isoOfCompatibleTerms_eq_matrixHom (hd : 0 < d) :
    (isoOfCompatibleTerms i i' hq hq' e eK hs).hom =
      matrixHom (weightMatrix
        (pointTransformation (isoOfCompatibleTerms i i' hq hq' e eK hs).hom)) :=
  eq_matrixHom_of_hasScalarWeight _ hd
    (isoOfCompatibleTerms_hasScalarWeight i i' hq hq' e eK hs a a' d ha ha' he)

/-- The same quotient-transition matrix works on every scheme test. -/
theorem coordinates_isoOfCompatibleTerms (hd : 0 < d) (T : Over (Spec R))
    (x : T ⟶ (groupScheme R n).X) :
    (coordinates R m T (x ≫ (isoOfCompatibleTerms i i' hq hq' e eK hs).hom.hom.hom)).toAdd =
      (weightMatrix
        (pointTransformation (isoOfCompatibleTerms i i' hq hq' e eK hs).hom)).map
          (scalarMap T) *ᵥ (coordinates R n T x).toAdd :=
  coordinates_of_hasScalarWeight _ hd
    (isoOfCompatibleTerms_hasScalarWeight i i' hq hq' e eK hs a a' d ha ha' he) T x

end Langlands.GroupScheme.FppfQuotientComparison
