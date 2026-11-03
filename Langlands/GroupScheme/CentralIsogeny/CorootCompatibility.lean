import Langlands.GroupScheme.Reductive.RootDatumCorootComparison
import Langlands.GroupScheme.Rational.RelativeWeylCharacterAction
import Langlands.GroupScheme.ConjugacyBaseChange

/-! # Actual torus reflections and coroot compatibility in a commuting square -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The actual involution of a commutative group scheme defined by a character and a
cocharacter pairing to two. -/
def latticeReflectionIso (α : characterLattice T) (ν : cocharacterLattice T)
    (h : latticePairing T α ν = 2) : T ≅ T := by
  let a : T ⟶ T := α ≫ ν
  have hνα : ν ≫ α = (2 : ℤ) • 𝟙 (Gm (Spec (CommRingCat.of k))) := by
    rw [eq_gmEndEquiv_zsmul k (ν ≫ α)]
    exact congrArg (fun n : ℤ => n • 𝟙 (Gm (Spec (CommRingCat.of k)))) h
  have ha : a ≫ a = (2 : ℤ) • a := by
    change (α ≫ ν) ≫ (α ≫ ν) = _
    calc
      (α ≫ ν) ≫ (α ≫ ν) = (α ≫ (ν ≫ α)) ≫ ν := by simp only [Category.assoc]
      _ = (2 : ℤ) • (α ≫ ν) := by
        rw [hνα, Preadditive.comp_zsmul, Category.comp_id, Preadditive.zsmul_comp]
  have hr : (𝟙 T - a) ≫ (𝟙 T - a) = 𝟙 T := by
    rw [Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.comp_sub,
      Category.id_comp, Category.id_comp, Category.comp_id, ha]
    module
  exact ⟨𝟙 T - a, 𝟙 T - a, hr, hr⟩

@[simp]
theorem latticeReflectionIso_hom (α : characterLattice T) (ν : cocharacterLattice T)
    (h : latticePairing T α ν = 2) :
    (latticeReflectionIso α ν h).hom = 𝟙 T - α ≫ ν := rfl

@[simp]
theorem latticeReflectionIso_inv (α : characterLattice T) (ν : cocharacterLattice T)
    (h : latticePairing T α ν = 2) :
    (latticeReflectionIso α ν h).inv = 𝟙 T - α ≫ ν := rfl

/-- The actual involution induces the usual reflection formula on every character. -/
theorem characterAut_latticeReflectionIso (α : characterLattice T)
    (ν : cocharacterLattice T) (h : latticePairing T α ν = 2)
    (χ : characterLattice T) :
    characterAut (latticeReflectionIso α ν h) χ = χ - latticePairing T χ ν • α := by
  change (𝟙 T - α ≫ ν) ≫ χ = _
  rw [Preadditive.sub_comp, Category.id_comp, Category.assoc,
    eq_gmEndEquiv_zsmul k (ν ≫ χ), Preadditive.comp_zsmul, Category.comp_id]
  rfl

/-- Matching roots make the two actual reflection endomorphisms commute with the torus map. -/
theorem latticeReflectionIso_hom_comp (t : T ⟶ T')
    (α : characterLattice T) (α' : characterLattice T') (ν : cocharacterLattice T)
    (h : latticePairing T α ν = 2)
    (h' : latticePairing T' α' (ν ≫ t) = 2) (hα : t ≫ α' = α) :
    (latticeReflectionIso α ν h).hom ≫ t =
      t ≫ (latticeReflectionIso α' (ν ≫ t) h').hom := by
  simp only [latticeReflectionIso_hom, Preadditive.sub_comp, Preadditive.comp_sub,
    Category.id_comp, Category.comp_id, ← Category.assoc, hα]

section ActualReflection

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) {J : Type v}
  {P : RootDatum J (characterLattice T) (cocharacterLattice T)}

/-- A supplied actual root datum realizes the explicit character/cocharacter reflection
by an actual normalizing point. -/
theorem IsRootDatumOf.exists_normalizing_latticeReflectionIso
    (hP : IsRootDatumOf i P) (hT : IsSplitTorus T.toGrp) (j : J) :
    ∃ n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      IsNormalizingPoint i n (latticeReflectionIso (P.root j) (P.coroot j)
        (by rw [← hP.1]; exact P.root_coroot_two j)) := by
  obtain ⟨n, σ, hn, hσ⟩ := hP.2.2 j
  let e := latticeReflectionIso (P.root j) (P.coroot j)
    (by rw [← hP.1]; exact P.root_coroot_two j)
  have hinv : σ.inv = e.hom := by
    apply hT.hom_ext_characters
    intro χ
    have he := characterAut_latticeReflectionIso (P.root j) (P.coroot j)
      (by rw [← hP.1]; exact P.root_coroot_two j) χ
    have hs := congrArg (fun s : characterLattice T ≃ₗ[ℤ] characterLattice T => s χ) hσ
    change σ.inv ≫ χ = P.reflection j χ at hs
    rw [RootPairing.reflection_apply] at hs
    change σ.inv ≫ χ = χ - P.toLinearMap χ (P.coroot j) • P.root j at hs
    rw [hP.1] at hs
    exact hs.trans he.symm
  have hhom : σ.hom = e.hom := by
    apply (cancel_mono σ.inv).mp
    rw [Iso.hom_inv_id, hinv]
    exact e.hom_inv_id.symm
  have hσe : σ = e := Iso.ext hhom
  refine ⟨n, ?_⟩
  change IsNormalizingPoint i n e
  rw [← hσe]
  exact hn

end ActualReflection

section Square

variable {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ H)
  (φ : G ⟶ H) (t : T ⟶ T')
  (hsquare : i ≫ φ = CommGroupScheme.groupHom t ≫ i')

include hsquare

omit [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
/-- An actual source reflection maps to the corresponding actual target reflection whenever
the torus map is epimorphic and their roots match by character pullback. -/
theorem IsNormalizingPoint.map_latticeReflectionIso
    [Epi (CommGroupScheme.groupHom t)]
    {α : characterLattice T} {α' : characterLattice T'} {ν : cocharacterLattice T}
    (h : latticePairing T α ν = 2) (h' : latticePairing T' α' (ν ≫ t) = 2)
    (hα : t ≫ α' = α)
    {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hn : IsNormalizingPoint i n (latticeReflectionIso α ν h)) :
    IsNormalizingPoint i' (n ≫ φ.hom.hom) (latticeReflectionIso α' (ν ≫ t) h') := by
  apply (cancel_epi (CommGroupScheme.groupHom t)).mp
  calc
    CommGroupScheme.groupHom t ≫ i' ≫ (H.innerIso (n ≫ φ.hom.hom)).hom =
        i ≫ φ ≫ (H.innerIso (n ≫ φ.hom.hom)).hom := by rw [← Category.assoc, ← hsquare, Category.assoc]
    _ = (i ≫ (G.innerIso n).hom) ≫ φ := by rw [Category.assoc, innerIso_hom_comp]
    _ = (CommGroupScheme.groupHom (latticeReflectionIso α ν h).hom ≫ i) ≫ φ :=
      congrArg (fun f => f ≫ φ) hn
    _ = (CommGroupScheme.groupHom (latticeReflectionIso α ν h).hom ≫
        CommGroupScheme.groupHom t) ≫ i' := by rw [Category.assoc, hsquare, ← Category.assoc]
    _ = CommGroupScheme.groupHom t ≫ CommGroupScheme.groupHom
        (latticeReflectionIso α' (ν ≫ t) h').hom ≫ i' := by
      have he := congrArg CommGroupScheme.groupHom
        (latticeReflectionIso_hom_comp t α α' ν h h' hα)
      change CommGroupScheme.groupHom (latticeReflectionIso α ν h).hom ≫
        CommGroupScheme.groupHom t = CommGroupScheme.groupHom t ≫
          CommGroupScheme.groupHom (latticeReflectionIso α' (ν ≫ t) h').hom at he
      rw [he, Category.assoc]

variable {J : Type v} {J' : Type w}
  {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
  {Q : RootDatum J' (characterLattice T') (cocharacterLattice T')}

/-- For supplied actual root data, matching roots have compatible coroots in an epimorphic
torus square, provided the target full normalizer image is finite. -/
theorem IsRootDatumOf.coroot_comp_of_finite_weylImage
    (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf i' Q)
    (hT : IsSplitTorus T.toGrp) [Epi (CommGroupScheme.groupHom t)]
    [Mono i'.hom.hom.left] [Finite (weylImage i')]
    {j : J} {j' : J'} (hroot : t ≫ Q.root j' = P.root j) :
    P.coroot j ≫ t = Q.coroot j' := by
  have h : latticePairing T (P.root j) (P.coroot j) = 2 := by
    rw [← hP.1]
    exact P.root_coroot_two j
  have h' : latticePairing T' (Q.root j') (P.coroot j ≫ t) = 2 := by
    change gmEndEquiv k ((P.coroot j ≫ t) ≫ Q.root j') = 2
    rw [Category.assoc, hroot]
    exact h
  let e := latticeReflectionIso (Q.root j') (P.coroot j ≫ t) h'
  obtain ⟨n, hn⟩ := hP.exists_normalizing_latticeReflectionIso i hT j
  have hn' : IsNormalizingPoint i' (n ≫ φ.hom.hom) e :=
    IsNormalizingPoint.map_latticeReflectionIso i i' φ t hsquare h h' hroot hn
  obtain ⟨m, τ, hm, hτ⟩ := hQ.2.2 j'
  let n' : normalizerPoints i' := ⟨n ≫ φ.hom.hom, e, hn'⟩
  let m' : normalizerPoints i' := ⟨m, τ, hm⟩
  have hs : weylAction i' n' = characterAut e := by
    ext χ
    exact weylAction_eq i' (n := n') (σ := e) hn' χ
  have ht : weylAction i' m' = Q.reflection j' := by
    ext χ
    rw [weylAction_eq i' (n := m') (σ := τ) hm χ]
    change characterAut τ χ = _
    rw [hτ]
  let a : weylImage i' := ⟨weylAction i' n', n', rfl⟩
  let b : weylImage i' := ⟨weylAction i' m', m', rfl⟩
  have horder : IsOfFinOrder (characterAut e * Q.reflection j') := by
    have hfin := (weylImage i').subtype.isOfFinOrder (isOfFinOrder_of_finite (a * b))
    change IsOfFinOrder (weylAction i' n' * weylAction i' m') at hfin
    rwa [hs, ht] at hfin
  let f := (latticePairing T').flip (P.coroot j ≫ t)
  let g := (latticePairing T').flip (Q.coroot j')
  have hg : g (Q.root j') = 2 := by
    change latticePairing T' (Q.root j') (Q.coroot j') = 2
    rw [← hQ.1]
    exact Q.root_coroot_two j'
  have heq := Langlands.LinearAlgebra.eq_functional_of_finiteOrder_reflections
    (Q.root j') f g (characterAut e) (Q.reflection j') h' hg
    (characterAut_latticeReflectionIso (Q.root j') (P.coroot j ≫ t) h')
    (fun χ => by
      rw [RootPairing.reflection_apply]
      change χ - Q.toLinearMap χ (Q.coroot j') • Q.root j' = _
      rw [hQ.1]
      rfl) horder
  apply Q.flip.toPerfPair.injective
  ext χ
  change Q.toLinearMap χ (P.coroot j ≫ t) = Q.toLinearMap χ (Q.coroot j')
  rw [hQ.1]
  exact LinearMap.congr_fun heq χ

end Square

end Langlands.GroupScheme
