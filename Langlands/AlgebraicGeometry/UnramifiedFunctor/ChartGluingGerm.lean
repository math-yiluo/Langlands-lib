import Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluingAdic
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreBaseChangeColimits
import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-! # Spreading out a factorization from a local ring (SGA 3, XI 3.1)

Let `ξ ∈ F(U)` be a monomorphism `U → F`, infinitesimally étale at every point, with `U`
locally of finite type over `S`, and let `F` satisfy (F1a), (F1b), (F2) and (F3). This module
proves that if `η ∈ F(T)` factors through `ξ` at the residue field of a point `t` of `T` at
which `T` is locally noetherian (in the sense that the stalk is noetherian and `T` is germ
injective at `t`), then `η` factors through `ξ` on an open neighbourhood of `t`.

The factorization on `Spec 𝒪_{T,t}` from `ChartGluingAdic` spreads out to a morphism
`V ⟶ U` on an open neighbourhood `V` of `t` (Mathlib's `spread_out_of_isGermInjective'`);
two elements of `F(V)` that agree on `Spec 𝒪_{T,t}` agree near `t`, because by (F2) the
functor `B ↦ F(Spec B)` commutes with the filtered colimit `R_P = colim_{g ∉ P} R_g`. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.UnramifiedFunctor.BaseChange

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluing

/-! ### Filtered colimits of rings under a ring -/

section UnderColimit

variable {J : Type u} [SmallCategory J] [IsFiltered J] {R : CommRingCat.{u}} {D : J ⥤ Under R}

/-- A cocone in `Under R` over a filtered diagram is a colimit as soon as it is a colimit on
underlying sets. -/
def isColimitOfElements (c : Cocone D)
    (hsurj : ∀ x : c.pt.right, ∃ (j : J) (y : (D.obj j).right), (c.ι.app j).right y = x)
    (hinj : ∀ (j : J) (x y : (D.obj j).right), (c.ι.app j).right x = (c.ι.app j).right y →
      ∃ (k : J) (f : j ⟶ k), (D.map f).right x = (D.map f).right y) :
    IsColimit c := by
  have : IsConnected J := IsFiltered.isConnected J
  have : ReflectsColimitsOfShape J (forget CommRingCat.{u}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (Under.forget R) (isColimitOfReflects (forget CommRingCat.{u}) ?_)
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    obtain ⟨j, y, hy⟩ := hsurj x
    exact ⟨j, y, hy.symm⟩
  · intro j x y h
    exact hinj j x y h

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v} {h : Spec R ⟶ S}

lemma exists_eq_of_isColimit (hG : Good F h) {c : Cocone D} (hc : IsColimit c) {j : J}
    (x y : (specOver h ⋙ F).obj (D.obj j))
    (hxy : (specOver h ⋙ F).map (c.ι.app j) x = (specOver h ⋙ F).map (c.ι.app j) y) :
    ∃ (k : J) (f : j ⟶ k),
      (specOver h ⋙ F).map (D.map f) x = (specOver h ⋙ F).map (D.map f) y := by
  have := hG.preserves_filtered_colimits J
  exact (Types.FilteredColimit.isColimit_eq_iff' (isColimitOfPreserves (specOver h ⋙ F) hc)
    x y).mp hxy

lemma exists_of_isColimit (hG : Good F h) {c : Cocone D} (hc : IsColimit c)
    (z : (specOver h ⋙ F).obj c.pt) :
    ∃ (j : J) (x : (specOver h ⋙ F).obj (D.obj j)), (specOver h ⋙ F).map (c.ι.app j) x = z := by
  have := hG.preserves_filtered_colimits J
  exact Types.jointly_surjective_of_isColimit (isColimitOfPreserves (specOver h ⋙ F) hc) z

variable (h) in
/-- The structure morphism `Spec B ⟶ Spec R` of a ring `B` under `R`, over `S`. -/
def underBase (B : Under R) : ((specOver h).obj B).unop ⟶ Over.mk h :=
  Over.homMk (Spec.map B.hom)

lemma specOver_map_comp_underBase {B B' : Under R} (u : B ⟶ B') :
    ((specOver h).map u).unop ≫ underBase h B = underBase h B' := by
  apply Over.OverMorphism.ext
  change Spec.map u.right ≫ Spec.map B.hom = Spec.map B'.hom
  rw [← Spec.map_comp, Under.w u]

lemma map_underBase {B B' : Under R} (u : B ⟶ B') (α : F.obj (op (Over.mk h))) :
    (specOver h ⋙ F).map u (F.map (underBase h B).op α) = F.map (underBase h B').op α := by
  rw [← specOver_map_comp_underBase u, op_comp, Quiver.Hom.op_unop, Functor.map_comp_apply]
  rfl

end UnderColimit

/-! ### A localization at a prime as a filtered colimit -/

section Localization

variable {R : Type u} [CommRing R] (P : Ideal R) [P.IsPrime]

/-- The elements outside a prime ideal `P`, preordered by divisibility. -/
structure DivIdx where
  /-- The element. -/
  elt : R
  mem : elt ∈ P.primeCompl

instance : Preorder (DivIdx P) where
  le a b := a.elt ∣ b.elt
  le_refl a := dvd_refl a.elt
  le_trans _ _ _ := dvd_trans

instance : IsDirectedOrder (DivIdx P) where
  directed a b := ⟨⟨a.elt * b.elt, P.primeCompl.mul_mem a.mem b.mem⟩,
    dvd_mul_right a.elt b.elt, dvd_mul_left b.elt a.elt⟩

instance : Nonempty (DivIdx P) := ⟨⟨1, P.primeCompl.one_mem⟩⟩

variable {P}

/-- The transition map `R_a → R_b` for `a ∣ b`. -/
def locMap {a b : DivIdx P} (hab : a ≤ b) :
    Localization.Away a.elt →+* Localization.Away b.elt :=
  IsLocalization.Away.lift a.elt (IsLocalization.Away.isUnit_of_dvd b.elt hab)

lemma locMap_algebraMap {a b : DivIdx P} (hab : a ≤ b) (r : R) :
    locMap hab (algebraMap R _ r) = algebraMap R _ r :=
  IsLocalization.Away.lift_eq _ _ r

lemma locMap_ext {a : DivIdx P} {T : Type*} [CommRing T]
    {f g : Localization.Away a.elt →+* T} (h : ∀ r, f (algebraMap R _ r) = g (algebraMap R _ r)) :
    f = g :=
  IsLocalization.ringHom_ext (Submonoid.powers a.elt) (RingHom.ext h)

variable (P)

/-- The diagram `a ↦ R_a` of rings under `R`, for `a ∉ P`. -/
def locDiagram : DivIdx P ⥤ Under (CommRingCat.of R) where
  obj a := Under.mk (CommRingCat.ofHom (algebraMap R (Localization.Away a.elt)))
  map {a b} f := Under.homMk (CommRingCat.ofHom (locMap (leOfHom f)))
    (CommRingCat.hom_ext (RingHom.ext fun r ↦ locMap_algebraMap (leOfHom f) r))
  map_id a := by
    refine Under.UnderMorphism.ext (CommRingCat.hom_ext (locMap_ext fun r ↦ ?_))
    change locMap (leOfHom (𝟙 a)) (algebraMap R _ r) = algebraMap R _ r
    rw [locMap_algebraMap]
  map_comp {a b c} f g := by
    refine Under.UnderMorphism.ext (CommRingCat.hom_ext (locMap_ext fun r ↦ ?_))
    change locMap (leOfHom (f ≫ g)) (algebraMap R _ r) =
      locMap (leOfHom g) (locMap (leOfHom f) (algebraMap R _ r))
    rw [locMap_algebraMap, locMap_algebraMap, locMap_algebraMap]

variable (L : Type u) [CommRing L] [Algebra R L] [IsLocalization.AtPrime L P]

/-- The map `R_a → R_P` for `a ∉ P`. -/
def locToAtPrime (a : DivIdx P) : Localization.Away a.elt →+* L :=
  IsLocalization.Away.lift a.elt (IsLocalization.map_units L (⟨a.elt, a.mem⟩ : P.primeCompl))

lemma locToAtPrime_algebraMap (a : DivIdx P) (r : R) :
    locToAtPrime P L a (algebraMap R _ r) = algebraMap R L r :=
  IsLocalization.Away.lift_eq _ _ r

/-- `R_P` as a cocone over the diagram `a ↦ R_a`. -/
def locCocone : Cocone (locDiagram P) where
  pt := Under.mk (CommRingCat.ofHom (algebraMap R L))
  ι :=
    { app a := Under.homMk (CommRingCat.ofHom (locToAtPrime P L a) :
          CommRingCat.of (Localization.Away a.elt) ⟶ CommRingCat.of L)
        (CommRingCat.hom_ext (RingHom.ext fun r ↦ locToAtPrime_algebraMap P L a r))
      naturality a b f := by
        refine Under.UnderMorphism.ext (CommRingCat.hom_ext (locMap_ext fun r ↦ ?_))
        change locToAtPrime P L b (locMap (leOfHom f) (algebraMap R _ r)) =
          locToAtPrime P L a (algebraMap R _ r)
        rw [locMap_algebraMap, locToAtPrime_algebraMap, locToAtPrime_algebraMap] }

/-- `R_P` is the filtered colimit of the `R_a`, `a ∉ P`. -/
def isColimitLocCocone : IsColimit (locCocone P L) := by
  refine isColimitOfElements _ ?_ ?_
  · intro (x : L)
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    refine ⟨⟨s.1, s.2⟩, IsLocalization.mk' (Localization.Away s.1) r
      (⟨s.1, Submonoid.mem_powers _⟩ : Submonoid.powers s.1), ?_⟩
    change locToAtPrime P L _ _ = _
    rw [IsLocalization.eq_mk'_iff_mul_eq, ← locToAtPrime_algebraMap P L ⟨s.1, s.2⟩, ← map_mul,
      IsLocalization.mk'_spec, locToAtPrime_algebraMap]
  · intro j (x : Localization.Away j.elt) (y : Localization.Away j.elt) hxy
    change locToAtPrime P L j x = locToAtPrime P L j y at hxy
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers j.elt) (x - y)
    have ha : algebraMap R L a = 0 := by
      have := congrArg (locToAtPrime P L j) hs
      rw [map_mul, map_sub, hxy, sub_self, zero_mul, locToAtPrime_algebraMap] at this
      exact this.symm
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl L a).mp ha
    let k : DivIdx P := ⟨j.elt * m.1, P.primeCompl.mul_mem j.mem m.2⟩
    have hjk : j ≤ k := dvd_mul_right j.elt m.1
    refine ⟨k, homOfLE hjk, ?_⟩
    change locMap hjk x = locMap hjk y
    rw [← sub_eq_zero, ← map_sub]
    have hs' : IsUnit (algebraMap R (Localization.Away k.elt) s.1) := by
      obtain ⟨n, hn⟩ := s.2
      rw [← hn, map_pow]
      exact (IsLocalization.Away.isUnit_of_dvd k.elt hjk).pow n
    have hmu : IsUnit (algebraMap R (Localization.Away k.elt) m.1) :=
      IsLocalization.Away.isUnit_of_dvd k.elt (dvd_mul_left m.1 j.elt)
    have ha' : algebraMap R (Localization.Away k.elt) a = 0 := by
      rw [← hmu.mul_right_eq_zero, ← map_mul, hm, map_zero]
    have := congrArg (locMap hjk) hs
    rw [map_mul, locMap_algebraMap, locMap_algebraMap, ha', hs'.mul_left_eq_zero] at this
    exact this

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}

/-- Germs along a prime (F2): two elements of `F(Spec R)` with the same restriction to the
localization `R_P` have the same restriction to some `R_g`, `g ∉ P`. -/
theorem exists_away_eq_of_atPrime (hZ : ZariskiSheaf F) (h2 : FilteredColimits F)
    (f : Spec (CommRingCat.of R) ⟶ S) (α β : F.obj (op (Over.mk f)))
    (hαβ : F.map (algebraOverBase f L).op α = F.map (algebraOverBase f L).op β) :
    ∃ g ∉ P, F.map (algebraOverBase f (Localization.Away g)).op α =
      F.map (algebraOverBase f (Localization.Away g)).op β := by
  have hG := good_all hZ h2 f
  let one : DivIdx P := ⟨1, P.primeCompl.one_mem⟩
  obtain ⟨k, u, hk⟩ := exists_eq_of_isColimit hG (isColimitLocCocone P L) (j := one)
    (F.map (underBase f _).op α) (F.map (underBase f _).op β) (by
      rw [map_underBase, map_underBase]
      exact hαβ)
  rw [map_underBase, map_underBase] at hk
  exact ⟨k.elt, k.mem, hk⟩

end Localization

/-! ### Germs of elements on schemes -/

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}

/-- Two elements of `F(T)` with the same restriction to `Spec R_P`, for an open immersion
`Spec R ⟶ T`, agree on an open neighbourhood of the image of `P`. -/
theorem exists_opens_eq_of_isOpenImmersion (hZ : ZariskiSheaf F) (h2 : FilteredColimits F)
    {T : Over S} {R : Type u} [CommRing R] (j : Spec (CommRingCat.of R) ⟶ T.left)
    [IsOpenImmersion j] (P : Ideal R) [P.IsPrime] (L : Type u) [CommRing L] [Algebra R L]
    [IsLocalization.AtPrime L P] (α β : F.obj (op T))
    (h : F.map (algebraOverBase (j ≫ T.hom) L ≫ (Over.homMk j : Over.mk (j ≫ T.hom) ⟶ T)).op α =
      F.map (algebraOverBase (j ≫ T.hom) L ≫ (Over.homMk j : Over.mk (j ≫ T.hom) ⟶ T)).op β) :
    ∃ V : T.left.Opens, j (⟨P, inferInstance⟩ : PrimeSpectrum R) ∈ V ∧
      F.map (ιOver T V).op α = F.map (ιOver T V).op β := by
  let c : Over.mk (j ≫ T.hom) ⟶ T := Over.homMk j
  obtain ⟨g, hg, hαβ⟩ := exists_away_eq_of_atPrime P L hZ h2 (j ≫ T.hom) (F.map c.op α)
    (F.map c.op β) (by rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, h])
  let cg := algebraOverBase (j ≫ T.hom) (Localization.Away g) ≫ c
  have : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))) :=
    IsOpenImmersion.of_isLocalization g
  have : IsOpenImmersion cg.left := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g))) ≫ j)
    infer_instance
  obtain ⟨q, hq⟩ : (⟨P, inferInstance⟩ : PrimeSpectrum R) ∈ Set.range
      (PrimeSpectrum.comap (algebraMap R (Localization.Away g))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
    exact hg
  have htg : j (⟨P, inferInstance⟩ : PrimeSpectrum R) ∈ Set.range cg.left :=
    ⟨q, (Scheme.Hom.comp_apply _ _ _).trans (congrArg j hq)⟩
  refine ⟨cg.left.opensRange, htg, ?_⟩
  rw [ιOver_opensRange cg, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, op_comp,
    Functor.map_comp_apply, Functor.map_comp_apply, hαβ]


/-- `Spec.map` of the germ map `Γ(T, W) → 𝒪_{T,t}` followed by the inclusion of `W` is the
canonical morphism `Spec 𝒪_{T,t} ⟶ T`. -/
lemma specMap_germ_fromSpec {X : Scheme.{u}} {W : X.Opens} (hW : IsAffineOpen W) {t : X}
    (htW : t ∈ W) : Spec.map (X.presheaf.germ W t htW) ≫ hW.fromSpec = X.fromSpecStalk t := by
  rw [← IsAffineOpen.fromSpecStalk, hW.fromSpecStalk_eq_fromSpecStalk htW]

/-- The identity of `Spec 𝒪_{T,t}`, from the spectrum of `𝒪_{T,t}` as an algebra over the
sections over an affine open neighbourhood `W` of `t`, to the source of `stalkPt T t`. -/
def stalkAlgebraToStalkPt {T : Over S} {W : T.left.Opens} (hW : IsAffineOpen W)
    {t : T.left} (htW : t ∈ W) :
    letI := TopCat.Presheaf.algebra_section_stalk T.left.presheaf ⟨t, htW⟩
    algebraOver (hW.fromSpec ≫ T.hom) (T.left.presheaf.stalk t) ⟶
      Over.mk (T.left.fromSpecStalk t ≫ T.hom) :=
  letI := TopCat.Presheaf.algebra_section_stalk T.left.presheaf ⟨t, htW⟩
  Over.homMk (𝟙 (Spec (CommRingCat.of (T.left.presheaf.stalk t)))) (by
    show 𝟙 (Spec (CommRingCat.of (T.left.presheaf.stalk t))) ≫ T.left.fromSpecStalk t ≫ T.hom =
      Spec.map (T.left.presheaf.germ W t htW) ≫ hW.fromSpec ≫ T.hom
    rw [Category.id_comp, ← Category.assoc, specMap_germ_fromSpec hW htW])

lemma stalkAlgebraToStalkPt_comp {T : Over S} {W : T.left.Opens} (hW : IsAffineOpen W)
    {t : T.left} (htW : t ∈ W) :
    letI := TopCat.Presheaf.algebra_section_stalk T.left.presheaf ⟨t, htW⟩
    stalkAlgebraToStalkPt hW htW ≫ stalkPt T t =
      algebraOverBase (hW.fromSpec ≫ T.hom) (T.left.presheaf.stalk t) ≫
        (Over.homMk hW.fromSpec : Over.mk (hW.fromSpec ≫ T.hom) ⟶ T) := by
  apply Over.OverMorphism.ext
  show 𝟙 (Spec (CommRingCat.of (T.left.presheaf.stalk t))) ≫ T.left.fromSpecStalk t =
    Spec.map (T.left.presheaf.germ W t htW) ≫ hW.fromSpec
  rw [Category.id_comp, specMap_germ_fromSpec hW htW]

/-- Two elements of `F(T)` with the same restriction to `Spec 𝒪_{T,t}` agree on an open
neighbourhood of `t`. -/
theorem exists_opens_eq_of_stalkPt (hZ : ZariskiSheaf F) (h2 : FilteredColimits F)
    {T : Over S} (t : T.left) (α β : F.obj (op T))
    (h : F.map (stalkPt T t).op α = F.map (stalkPt T t).op β) :
    ∃ V : T.left.Opens, t ∈ V ∧ F.map (ιOver T V).op α = F.map (ιOver T V).op β := by
  obtain ⟨_, ⟨W, hW, rfl⟩, htW, -⟩ :=
    T.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ t) isOpen_univ
  have hW : IsAffineOpen W := hW
  let := TopCat.Presheaf.algebra_section_stalk T.left.presheaf ⟨t, htW⟩
  have := hW.isLocalization_stalk ⟨t, htW⟩
  have e := stalkAlgebraToStalkPt_comp hW htW
  obtain ⟨V, hV, hαβ⟩ := exists_opens_eq_of_isOpenImmersion hZ h2 hW.fromSpec
    (hW.primeIdealOf ⟨t, htW⟩).asIdeal (T.left.presheaf.stalk t) α β (by
      rw [← e, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, h])
  refine ⟨V, ?_, hαβ⟩
  convert hV
  exact (hW.fromSpec_primeIdealOf ⟨t, htW⟩).symm

/-- If `η|_X` factors through `ξ` near `x` for an open immersion `X ⟶ T`, then `η` factors
through `ξ` near the image of `x`. -/
lemma LocFac.of_map {U : Over S} {ξ : F.obj (op U)} {T X : Over S} {η : F.obj (op T)}
    (c : X ⟶ T) [IsOpenImmersion c.left] {x : X.left} (h : LocFac ξ (F.map c.op η) x) :
    LocFac ξ η (c.left x) := by
  obtain ⟨V, hV, hfac⟩ := h
  rw [fac_map_iff] at hfac
  have : IsOpenImmersion (ιOver X V ≫ c).left := by
    change IsOpenImmersion (V.ι ≫ c.left)
    infer_instance
  exact LocFac.of_isOpenImmersion _ hfac ⟨⟨x, hV⟩, rfl⟩

/-! ### Spreading out -/

variable {U : Over S} {ξ : F.obj (op U)}

set_option backward.isDefEq.respectTransparency false in
/-- SGA 3, XI 3.1, (iii) ⇒ (i) at a point where `T` is locally noetherian: if `η` factors
through `ξ` at the residue field of `t`, then it factors through `ξ` on an open
neighbourhood of `t`. -/
theorem locFac_of_mem_W (hmono : IsMonoElement F ξ) (hZ : ZariskiSheaf F)
    (hF : FaithfullyFlatSheaf F) (h2 : FilteredColimits F) (hA : AdicLimits F)
    (hét : ∀ y, InfinitesimallyEtaleAt F ξ y) [LocallyOfFiniteType U.hom] {T : Over S}
    (η : F.obj (op T)) (t : T.left) [T.left.IsGermInjectiveAt t]
    [IsNoetherianRing (T.left.presheaf.stalk t)] (ht : t ∈ W ξ η) : LocFac ξ η t := by
  obtain ⟨k, hk⟩ := fac_stalkPt hmono hF hét hA η t ht
  obtain ⟨V, htV, f, hfk, hfw⟩ := spread_out_of_isGermInjective' T.hom U.hom k.left (Over.w k)
  let TV : Over S := Over.mk (V.ι ≫ T.hom)
  let f' : TV ⟶ U := Over.homMk f hfw
  let σ : Over.mk (T.left.fromSpecStalk t ≫ T.hom) ⟶ TV :=
    Over.homMk (V.fromSpecStalkOfMem t htV) (by
      change V.fromSpecStalkOfMem t htV ≫ V.ι ≫ T.hom = T.left.fromSpecStalk t ≫ T.hom
      rw [← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι])
  have hσf : σ ≫ f' = k := Over.OverMorphism.ext hfk.symm
  have hσι : σ ≫ ιOver T V = stalkPt T t :=
    Over.OverMorphism.ext (Scheme.Opens.fromSpecStalkOfMem_ι V t htV)
  have hσ : F.map σ.op (F.map f'.op ξ) = F.map σ.op (F.map (ιOver T V).op η) := by
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hσf, hσι, hk]
  let ε : Over.mk (TV.left.fromSpecStalk ⟨t, htV⟩ ≫ TV.hom) ⟶
      Over.mk (T.left.fromSpecStalk t ≫ T.hom) :=
    Over.homMk (Spec.map (V.ι.stalkMap ⟨t, htV⟩)) (by
      have := Scheme.SpecMap_stalkMap_fromSpecStalk V.ι (x := ⟨t, htV⟩) =≫ T.hom
      simp only [Category.assoc] at this
      exact this)
  have hεσ : ε ≫ σ = stalkPt TV ⟨t, htV⟩ := by
    apply Over.OverMorphism.ext
    change Spec.map (V.ι.stalkMap ⟨t, htV⟩) ≫ V.fromSpecStalkOfMem t htV =
      V.toScheme.fromSpecStalk ⟨t, htV⟩
    rw [Scheme.Opens.fromSpecStalkOfMem, ← Category.assoc, ← Spec.map_comp, IsIso.inv_hom_id,
      Spec.map_id, Category.id_comp]
  have h' : F.map (stalkPt TV ⟨t, htV⟩).op (F.map f'.op ξ) =
      F.map (stalkPt TV ⟨t, htV⟩).op (F.map (ιOver T V).op η) := by
    rw [← hεσ, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hσ]
  obtain ⟨V', hV', heq⟩ := exists_opens_eq_of_stalkPt hZ h2 (T := TV) ⟨t, htV⟩ _ _ h'
  have hloc : LocFac (T := TV) ξ (F.map (ιOver T V).op η) (⟨t, htV⟩ : V) :=
    ⟨V', hV', (⟨ιOver TV V' ≫ f', by rw [op_comp, Functor.map_comp_apply, heq]⟩ :
      Fac ξ _ _)⟩
  have : IsOpenImmersion (ιOver T V).left := by
    change IsOpenImmersion V.ι
    infer_instance
  exact LocFac.of_map (ιOver T V) hloc

end Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluing
