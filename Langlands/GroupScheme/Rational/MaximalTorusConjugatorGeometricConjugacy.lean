import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Torus.MaximalBaseChangeStatement
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.HomConjugacy
import Langlands.GroupScheme.Torus.LatticeGalois

/-! # Geometric conjugacy step for the generic semisimple-centralizer case -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Lift

variable {S : Scheme.{u}} {T H G : GroupScheme S}

/-- A homomorphism whose points all lie in the range of a monomorphic homomorphism `i` factors
through `i`. -/
theorem exists_lift_of_forall_mem_range (i : H ⟶ G) [Mono i.hom.hom] (f : T ⟶ G)
    (h : ∀ (U : Over S) (x : U ⟶ T.X), x ≫ f.hom.hom ∈ (SubgroupFunctor.range i).carrier U) :
    ∃ f' : T ⟶ H, f' ≫ i = f := by
  classical
  choose s hs using fun (U : Over S) (x : U ⟶ T.X) => SubgroupFunctor.mem_range.1 (h U x)
  have hF : ∀ (U : Over S) (x : U ⟶ T.X), IsMonHom.monoidHom f.hom.hom U x = x ≫ f.hom.hom :=
    fun _ _ => rfl
  have hI : ∀ (U : Over S) (y : U ⟶ H.X), IsMonHom.monoidHom i.hom.hom U y = y ≫ i.hom.hom :=
    fun _ _ => rfl
  let φ : ∀ U : Over S, (U ⟶ T.X) →* (U ⟶ H.X) := fun U =>
    { toFun := s U
      map_one' := by
        apply (cancel_mono i.hom.hom).1
        rw [hs, ← hF, map_one, ← hI, map_one]
      map_mul' := fun x y => by
        apply (cancel_mono i.hom.hom).1
        rw [hs, ← hF, map_mul, hF, hF, ← hs U x, ← hs U y, ← hI, ← hI, ← map_mul, hI] }
  have hφ : ∀ {U U' : Over S} (a : U' ⟶ U) (x : U ⟶ T.X), φ U' (a ≫ x) = a ≫ φ U x := by
    intro U U' a x
    apply (cancel_mono i.hom.hom).1
    change s U' (a ≫ x) ≫ i.hom.hom = (a ≫ s U x) ≫ i.hom.hom
    rw [hs, Category.assoc, Category.assoc, hs]
  refine ⟨homOfPoints φ hφ, hom_ext_points fun U x => ?_⟩
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_homOfPoints]
  exact hs U x

end Lift

section Conjugacy

variable {Ω : Type u} [Field Ω] {G H : GroupScheme (Spec (CommRingCat.of Ω))}
  {T₀ T : CommGroupScheme (Spec (CommRingCat.of Ω))}

/-- Over an algebraically closed field, let `c` be a rational point of `G` whose conjugate of
the maximal torus `j₀` lies in a smooth connected affine closed subgroup `i : H ⟶ G`. Then a
rational point `h` of `H` and an isomorphism `φ : T₀ ≅ T` carry the conjugate onto any given
maximal torus `j` of `H`. -/
theorem exists_innerIso_comp_eq_of_conj_mem_range [IsAlgClosed Ω]
    (hconj : MaximalTorusConjugacyStatement.{u})
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    {j₀ : T₀.toGrp ⟶ G} {j : T.toGrp ⟶ H} {i : H ⟶ G} (hi : IsClosedSubgroup i)
    (hj₀ : IsMaximalTorus j₀) (hj : IsMaximalTorus j)
    (c : Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶ G.X)
    (hc : ∀ (U : Over (Spec (CommRingCat.of Ω))) (t : U ⟶ G.X),
      t ∈ (SubgroupFunctor.range j₀).carrier U →
        G.constantPoint c U * t * (G.constantPoint c U)⁻¹ ∈
          (SubgroupFunctor.range i).carrier U) :
    ∃ (h : Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶ H.X) (φ : T₀ ≅ T),
      j₀ ≫ (G.innerIso c).hom ≫ (G.innerIso (h ≫ i.hom.hom)).hom =
        CommGroupScheme.groupHom φ.hom ≫ j ≫ i := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  obtain ⟨f, hf⟩ := exists_lift_of_forall_mem_range i (j₀ ≫ (G.innerIso c).hom)
    (fun U x => by
      rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]
      exact hc U _ (SubgroupFunctor.mem_range.2 ⟨x, rfl⟩))
  have hmax : IsMaximalTorus (f ≫ i) := by
    rw [hf]
    exact (IsMaximalTorus.comp_iso_iff j₀ (G.innerIso c)).2 hj₀
  obtain ⟨g, φ, hg⟩ := hconj Ω H T₀ T f j (IsMaximalTorus.of_comp hi hmax) hj
  refine ⟨g, φ, ?_⟩
  rw [← Category.assoc, ← hf, Category.assoc, ← innerIso_hom_comp, ← Category.assoc, hg,
    Category.assoc]

end Conjugacy

section Range

variable {S : Scheme.{u}} {G : GroupScheme S} {T₀ T : CommGroupScheme S}

/-- If conjugation by `c` and then by `d` carries the torus `j₀` onto `j'` up to an isomorphism,
then a point lies in the range of `j₀` exactly when its conjugate by `d * c` lies in the range
of `j'`. -/
theorem mem_range_iff_of_innerIso_comp_eq {j₀ : T₀.toGrp ⟶ G} {j' : T.toGrp ⟶ G}
    (c d : Over.mk (𝟙 S) ⟶ G.X) (φ : T₀ ≅ T)
    (h : j₀ ≫ (G.innerIso c).hom ≫ (G.innerIso d).hom = CommGroupScheme.groupHom φ.hom ≫ j')
    (U : Over S) (t : U ⟶ G.X) :
    t ∈ (SubgroupFunctor.range j₀).carrier U ↔
      G.constantPoint (d * c) U * t * (G.constantPoint (d * c) U)⁻¹ ∈
        (SubgroupFunctor.range j').carrier U := by
  have hP : G.constantPoint (d * c) U = G.constantPoint d U * G.constantPoint c U := by
    rw [← constantPointHom_apply, map_mul, constantPointHom_apply, constantPointHom_apply]
  have hpt : ∀ x : U ⟶ G.X, x ≫ (G.innerIso c).hom.hom.hom ≫ (G.innerIso d).hom.hom.hom =
      G.constantPoint (d * c) U * x * (G.constantPoint (d * c) U)⁻¹ := by
    intro x
    rw [← Category.assoc, comp_innerIso_hom, comp_innerIso_hom, hP]
    group
  have hh : j₀.hom.hom ≫ (G.innerIso c).hom.hom.hom ≫ (G.innerIso d).hom.hom.hom =
      (CommGroupScheme.groupHom φ.hom).hom.hom ≫ j'.hom.hom := by
    simpa only [Grp.comp_hom_hom] using congrArg (fun f => f.hom.hom) h
  have hinv : (CommGroupScheme.groupHom φ.inv).hom.hom ≫
      (CommGroupScheme.groupHom φ.hom).hom.hom = 𝟙 _ := by
    change (CommGroupScheme.groupHom (φ.inv ≫ φ.hom)).hom.hom = _
    rw [φ.inv_hom_id]
    rfl
  rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨s ≫ (CommGroupScheme.groupHom φ.hom).hom.hom, ?_⟩
    rw [Category.assoc, ← hh, ← Category.assoc, hpt]
  · rintro ⟨r, hr⟩
    refine ⟨r ≫ (CommGroupScheme.groupHom φ.inv).hom.hom, ?_⟩
    apply (MulAut.conj (G.constantPoint (d * c) U)).injective
    rw [MulAut.conj_apply, MulAut.conj_apply, ← hpt, Category.assoc, Category.assoc, hh,
      ← Category.assoc (CommGroupScheme.groupHom φ.inv).hom.hom, hinv, Category.id_comp, hr]

end Range

section Transport

variable {S S' : Scheme.{u}} (β : S' ⟶ S) {M : GroupScheme S}

/-- A scheme over `S'`, regarded over `S` through `β`, maps to `S'` regarded over `S`. -/
def overMapToMk (V' : Over S') : (Over.map β).obj V' ⟶ Over.mk β :=
  Over.homMk V'.hom (by simp)

/-- Under the pullback points equivalence, conjugation by the constant family of a base point
`q'` corresponds to conjugation by the matching point `q` of `M` over `Over.mk β`. -/
theorem baseChangePointsEquiv_constantPoint_conj (q : Over.mk β ⟶ M.X)
    (q' : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange β).obj M).X)
    (hq : baseChangePointsEquiv β M (Over.mk (𝟙 S')) q' = overMapToMk β (Over.mk (𝟙 S')) ≫ q)
    (V' : Over S') (t' : V' ⟶ ((GroupScheme.baseChange β).obj M).X) :
    baseChangePointsEquiv β M V'
        (((GroupScheme.baseChange β).obj M).constantPoint q' V' * t' *
          (((GroupScheme.baseChange β).obj M).constantPoint q' V')⁻¹) =
      (overMapToMk β V' ≫ q) * baseChangePointsEquiv β M V' t' * (overMapToMk β V' ≫ q)⁻¹ := by
  have hC : baseChangePointsEquiv β M V'
      (((GroupScheme.baseChange β).obj M).constantPoint q' V') = overMapToMk β V' ≫ q := by
    unfold constantPoint
    rw [baseChangePointsEquiv_naturality, hq, ← Category.assoc]
    congr 1
  rw [map_mul, map_mul, map_inv, hC]

/-- A conjugation condition over `Over.mk β` gives the matching condition after base change. -/
theorem conj_mem_baseChange_of_forall (F E : SubgroupFunctor M) (q : Over.mk β ⟶ M.X)
    (q' : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange β).obj M).X)
    (hq : baseChangePointsEquiv β M (Over.mk (𝟙 S')) q' = overMapToMk β (Over.mk (𝟙 S')) ≫ q)
    (h : ∀ (V : Over S) (y : V ⟶ Over.mk β) (t : V ⟶ M.X), t ∈ F.carrier V →
      (y ≫ q) * t * (y ≫ q)⁻¹ ∈ E.carrier V)
    (V' : Over S') (t' : V' ⟶ ((GroupScheme.baseChange β).obj M).X)
    (ht : t' ∈ (F.baseChange β).carrier V') :
    ((GroupScheme.baseChange β).obj M).constantPoint q' V' * t' *
        (((GroupScheme.baseChange β).obj M).constantPoint q' V')⁻¹ ∈
      (E.baseChange β).carrier V' := by
  rw [SubgroupFunctor.mem_baseChange, baseChangePointsEquiv_constantPoint_conj β q q' hq]
  exact h _ (overMapToMk β V') _ ht

/-- A conjugation equivalence after base change gives the matching equivalence over
`Over.mk β`. -/
theorem forall_iff_of_baseChange (F E : SubgroupFunctor M) (q : Over.mk β ⟶ M.X)
    (q' : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange β).obj M).X)
    (hq : baseChangePointsEquiv β M (Over.mk (𝟙 S')) q' = overMapToMk β (Over.mk (𝟙 S')) ≫ q)
    (h : ∀ (V' : Over S') (t' : V' ⟶ ((GroupScheme.baseChange β).obj M).X),
      t' ∈ (F.baseChange β).carrier V' ↔
        ((GroupScheme.baseChange β).obj M).constantPoint q' V' * t' *
            (((GroupScheme.baseChange β).obj M).constantPoint q' V')⁻¹ ∈
          (E.baseChange β).carrier V')
    (V : Over S) (y : V ⟶ Over.mk β) (t : V ⟶ M.X) :
    t ∈ F.carrier V ↔ (y ≫ q) * t * (y ≫ q)⁻¹ ∈ E.carrier V := by
  let V' : Over S' := Over.mk y.left
  let e : (Over.map β).obj V' ≅ V := Over.isoMk (Iso.refl _) (by simpa [V'] using (Over.w y).symm)
  have hy : overMapToMk β V' = e.hom ≫ y := by
    ext
    simp [V', e, overMapToMk]
  have ht' : baseChangePointsEquiv β M V' ((baseChangePointsEquiv β M V').symm (e.hom ≫ t)) =
      e.hom ≫ t := MulEquiv.apply_symm_apply _ _
  have key := h V' ((baseChangePointsEquiv β M V').symm (e.hom ≫ t))
  rw [SubgroupFunctor.mem_baseChange, SubgroupFunctor.mem_baseChange,
    baseChangePointsEquiv_constantPoint_conj β q q' hq, ht', hy] at key
  have hiso : ∀ (P : SubgroupFunctor M) (x : V ⟶ M.X),
      x ∈ P.carrier V ↔ e.hom ≫ x ∈ P.carrier ((Over.map β).obj V') := fun P x =>
    ⟨fun hx => P.comp_mem e.hom hx, fun hx => by simpa using P.comp_mem e.inv hx⟩
  rw [hiso F, hiso E, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv]
  simpa only [Category.assoc] using key

end Transport

section Geometric

variable {k K Ω : Type u} [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra K Ω]

/-- **Geometric conjugacy step.** Let `j₀` be a maximal torus of a smooth affine group `G` over
`k`, let `i : H ⟶ G_K` be a closed subgroup that is smooth, affine and connected over `K`, with
a maximal torus `j`, and let `Ω` be an algebraically closed field over `K`. If the point
`c : Spec Ω ⟶ G_K` conjugates the base change of `j₀` into `H` over every test scheme, then a
point `h₁ : Spec Ω ⟶ H` makes `p = i(h₁) · c` conjugate the base change of `j₀` onto `j ≫ i`
over every test scheme. This is conditional on maximal-torus conjugacy over algebraically
closed fields and on the stability of maximal tori under field extension. -/
theorem exists_torusConjugator_of_conj_mem_range [IsAlgClosed Ω]
    (hconj : MaximalTorusConjugacyStatement.{u}) (hbc : MaximalTorusBaseChangeStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of k))} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {T₀ : CommGroupScheme (Spec (CommRingCat.of k))} {j₀ : T₀.toGrp ⟶ G}
    (hj₀ : IsMaximalTorus j₀)
    {H : GroupScheme (Spec (CommRingCat.of K))} [Smooth H.X.hom] [IsAffineHom H.X.hom]
    [ConnectedSpace H.X.left]
    {T : CommGroupScheme (Spec (CommRingCat.of K))} {j : T.toGrp ⟶ H} (hj : IsMaximalTorus j)
    {i : H ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G} (hi : IsClosedSubgroup i)
    (c : Over.mk (algebraBaseMap K Ω) ⟶
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X)
    (hc : ∀ (V : Over (Spec (CommRingCat.of K))) (y : V ⟶ Over.mk (algebraBaseMap K Ω))
        (t : V ⟶ ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X),
      t ∈ ((SubgroupFunctor.range j₀).baseChange (algebraBaseMap k K)).carrier V →
        (y ≫ c) * t * (y ≫ c)⁻¹ ∈ (SubgroupFunctor.range i).carrier V) :
    ∃ h₁ : Over.mk (algebraBaseMap K Ω) ⟶ H.X,
      ∀ (V : Over (Spec (CommRingCat.of K))) (y : V ⟶ Over.mk (algebraBaseMap K Ω))
        (t : V ⟶ ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X),
        t ∈ ((SubgroupFunctor.range j₀).baseChange (algebraBaseMap k K)).carrier V ↔
          (y ≫ ((h₁ ≫ i.hom.hom) * c)) * t * (y ≫ ((h₁ ≫ i.hom.hom) * c))⁻¹ ∈
            (SubgroupFunctor.range (j ≫ i)).carrier V := by
  let b := algebraBaseMap k K
  let β := algebraBaseMap K Ω
  let GK := (GroupScheme.baseChange b).obj G
  have : Smooth GK.X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom GK.X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : Smooth ((GroupScheme.baseChange β).obj H).X.hom := by
    change Smooth (pullback.snd H.X.hom β)
    infer_instance
  have : IsAffineHom ((GroupScheme.baseChange β).obj H).X.hom := by
    change IsAffineHom (pullback.snd H.X.hom β)
    infer_instance
  have : ConnectedSpace ((GroupScheme.baseChange β).obj H).X.left :=
    H.connectedSpace_baseChange_of_smooth_affine β
  let j₀K := (GroupScheme.baseChange b).map j₀
  have hj₀K : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj T₀) j₀K :=
    (hbc k K G T₀ j₀ hj₀.1 hj₀.2.1).1 hj₀
  have hj₀KΩ := (hbc K Ω GK ((CommGroupScheme.baseChange b).obj T₀) j₀K hj₀K.1 hj₀K.2.1).1 hj₀K
  have hjΩ := (hbc K Ω H T j hj.1 hj.2.1).1 hj
  have hiΩ : IsClosedSubgroup ((GroupScheme.baseChange β).map i) := hi.baseChange β
  let c' := (baseChangePointsEquiv β GK (Over.mk (𝟙 _))).symm
    (overMapToMk β (Over.mk (𝟙 _)) ≫ c)
  have hc' : baseChangePointsEquiv β GK (Over.mk (𝟙 _)) c' =
      overMapToMk β (Over.mk (𝟙 _)) ≫ c :=
    MulEquiv.apply_symm_apply _ _
  have hrange₀ : (SubgroupFunctor.range j₀).baseChange b = SubgroupFunctor.range j₀K :=
    (SubgroupFunctor.range_baseChangeHom b j₀).symm
  obtain ⟨h, φ, hφ⟩ := exists_innerIso_comp_eq_of_conj_mem_range hconj hiΩ hj₀KΩ hjΩ c'
    (fun U t ht => by
      rw [SubgroupFunctor.range_baseChangeHom]
      apply conj_mem_baseChange_of_forall β (SubgroupFunctor.range j₀K) _ c c' hc'
        (by rw [← hrange₀]; exact hc)
      rw [← SubgroupFunctor.range_baseChangeHom]
      exact ht)
  let s : Over.mk β ⟶ (Over.map β).obj (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) :=
    Over.homMk (𝟙 _) (by simp)
  have hs : overMapToMk β (Over.mk (𝟙 _)) ≫ s = 𝟙 _ := by
    ext
    simp [overMapToMk, s]
  let h₁ : Over.mk β ⟶ H.X := s ≫ baseChangePointsEquiv β H (Over.mk (𝟙 _)) h
  refine ⟨h₁, ?_⟩
  have hq : baseChangePointsEquiv β GK (Over.mk (𝟙 _))
      ((h ≫ ((GroupScheme.baseChange β).map i).hom.hom) * c') =
      overMapToMk β (Over.mk (𝟙 _)) ≫ ((h₁ ≫ i.hom.hom) * c) := by
    rw [map_mul, baseChangePointsEquiv_comp, hc', MonObj.comp_mul]
    congr 1
  apply forall_iff_of_baseChange β _ _ _ _ hq
  intro V' t'
  rw [hrange₀, ← SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.range_baseChangeHom,
    Functor.map_comp]
  exact mem_range_iff_of_innerIso_comp_eq c' _ φ hφ V' t'

end Geometric

end Langlands.GroupScheme
