import Langlands.Cohomology.AbelianSheafFlasque
import Langlands.Cohomology.CechFlasque
import Langlands.Cohomology.CechRefine
import Mathlib.Topology.Sheaves.AddCommGrpCat

/-! # Finite-cover Čech degree one and actual abelian sheaf cohomology -/

noncomputable section

universe w u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Langlands.Cohomology.AbelianSheafCechH1

open Cech

section Augmentation

variable {T : TopCat.{u}} (P : TopCat.Presheaf AddCommGrpCat.{u} T)
  {ι : Type w} (U : ι → Opens T)

/-- Restriction of a global section to the degree-zero Čech cochain. -/
def globalCochain : P.obj (op ⊤) →+ C P U 0 where
  toFun s σ := res le_top s
  map_zero' := by funext σ; exact map_zero _
  map_add' s t := by funext σ; exact map_add _ _ _

lemma d_globalCochain (s : P.obj (op ⊤)) :
    d P U 0 (globalCochain P U s) = 0 := by
  funext τ
  rw [d_apply, Fin.sum_univ_two]
  simp only [globalCochain, AddMonoidHom.coe_mk, ZeroHom.coe_mk, res_res,
    Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, Pi.zero_apply]
  exact add_neg_eq_zero.2 rfl

variable {P} in
lemma map_globalCochain {Q : TopCat.Presheaf AddCommGrpCat.{u} T} (φ : P ⟶ Q)
    (s : P.obj (op ⊤)) :
    map U φ 0 (globalCochain P U s) = globalCochain Q U (φ.app _ s) := by
  funext σ
  exact map_res φ le_top s

variable {P U} in
lemma zeroCocycle_compatible {z : C P U 0} (hz : d P U 0 z = 0) (a b : ι)
    {O : Opens T} (ha : O ≤ inter U (fun _ : Fin 1 => a))
    (hb : O ≤ inter U (fun _ : Fin 1 => b)) :
    res ha (z fun _ => a) = res hb (z fun _ => b) := by
  have hO : O ≤ inter U ![a, b] := by
    rw [inter_two]
    exact le_inf (ha.trans (inter_le_apply _ 0)) (hb.trans (inter_le_apply _ 0))
  have h := res_d_zero_pair z a b hO ha hb
  rw [hz, Pi.zero_apply, map_zero] at h
  exact (sub_eq_zero.1 h.symm).symm

variable (F : TopCat.Sheaf AddCommGrpCat.{u} T)

lemma globalCochain_injective (hcov : ⊤ ≤ iSup U) :
    Function.Injective (globalCochain F.1 U) := by
  intro s t h
  apply eq_of_locally F (fun a => inter U (fun _ : Fin 1 => a)) (fun _ => le_top)
    (hcov.trans (iSup_mono fun a => (inter_const_one a).ge))
  intro a
  exact congrFun h (fun _ => a)

/-- The augmented Čech complex of a sheaf on a full cover is exact in degree zero. -/
lemma exists_globalCochain_eq (hcov : ⊤ ≤ iSup U) (z : C F.1 U 0)
    (hz : d F.1 U 0 z = 0) :
    ∃ s : F.1.obj (op ⊤), globalCochain F.1 U s = z := by
  obtain ⟨s, hs⟩ := exists_gluing F (fun a => inter U (fun _ : Fin 1 => a))
    (fun _ => le_top) (hcov.trans (iSup_mono fun a => (inter_const_one a).ge))
    (fun a => z fun _ => a)
    (fun a b => zeroCocycle_compatible hz a b inf_le_left inf_le_right)
  refine ⟨s, funext fun σ => ?_⟩
  obtain ⟨a, rfl⟩ : ∃ a, σ = fun _ => a :=
    ⟨σ 0, by funext a; rw [Fin.fin_one_eq_zero a]⟩
  exact hs a

end Augmentation

section Representatives

variable {T : TopCat.{u}} {ι : Type w} {U : ι → Opens T}
  {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)}

/-- A primitive of the image of a one-cochain, together with its glued quotient section. -/
structure Representative (z : C S.X₁.1 U 1) where
  primitive : C S.X₂.1 U 0
  quotientSection : S.X₃.1.obj (op ⊤)
  primitive_d : d S.X₂.1 U 0 primitive = map U S.f.hom 1 z
  quotient : map U S.g.hom 0 primitive = globalCochain S.X₃.1 U quotientSection

lemma g_f_section (V : Opens T) (a : S.X₁.1.obj (op V)) :
    S.g.hom.app (op V) (S.f.hom.app (op V) a) = 0 :=
  congrArg (fun φ : S.X₁ ⟶ S.X₃ => φ.hom.app (op V) a) S.zero

lemma f_section_injective (hS : S.ShortExact) (V : Opens T) :
    Function.Injective (S.f.hom.app (op V)) := by
  have := hS.mono_f
  have : Mono S.f.hom := (TopCat.Sheaf.forget AddCommGrpCat T).map_mono S.f
  exact (AddCommGrpCat.mono_iff_injective _).1 inferInstance

lemma exists_representative [Finite ι] (hcov : ⊤ ≤ iSup U)
    [TopCat.Presheaf.IsFlasque S.X₂.1] (z : C S.X₁.1 U 1)
    (hz : d S.X₁.1 U 1 z = 0) : Nonempty (Representative (S := S) z) := by
  obtain ⟨t, ht⟩ := exactAt_of_isFlasque S.X₂ U 0 (map U S.f.hom 1 z) (by
    rw [d_map, hz, map_zero])
  have hq : d S.X₃.1 U 0 (map U S.g.hom 0 t) = 0 := by
    rw [d_map, ht]
    funext σ
    exact g_f_section _ _
  obtain ⟨q, hq'⟩ := exists_globalCochain_eq U S.X₃ hcov _ hq
  exact ⟨⟨t, q, ht, hq'.symm⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual connecting class associated with a representative. -/
def Representative.value (hS : S.ShortExact) {z : C S.X₁.1 U 1}
    (r : Representative (S := S) z) : Sheaf.H.{u} S.X₁ 1 :=
  Sheaf.H.δ hS 0 1 rfl
    ((Sheaf.H.equiv₀ S.X₃ (isTerminalTop (α := Opens T))).symm r.quotientSection)

lemma map_g_f (p : ℕ) (c : C S.X₁.1 U p) :
    map U S.g.hom p (map U S.f.hom p c) = 0 := by
  funext σ
  exact g_f_section _ _

lemma map_f_injective (hS : S.ShortExact) (p : ℕ) :
    Function.Injective (map U S.f.hom p) := by
  intro x y h
  funext σ
  exact f_section_injective hS _ (congrFun h σ)

set_option backward.isDefEq.respectTransparency false in
lemma connecting_section_eq_zero_of_lift (hS : S.ShortExact)
    (s : S.X₂.1.obj (op ⊤)) :
    Sheaf.H.δ hS 0 1 rfl
      ((Sheaf.H.equiv₀ S.X₃ (isTerminalTop (α := Opens T))).symm
        (S.g.hom.app _ s)) = 0 := by
  rw [← Sheaf.H.equiv₀_symm_naturality]
  exact ConcreteCategory.congr_hom (Sheaf.H.longSequence_exact hS 0 1 rfl |>.zero 1) _

set_option backward.isDefEq.respectTransparency false in
/-- A representative's actual degree-one class vanishes precisely on Čech coboundaries. -/
theorem Representative.value_eq_zero_iff (hS : S.ShortExact) (hcov : ⊤ ≤ iSup U)
    {z : C S.X₁.1 U 1} (r : Representative (S := S) z) :
    r.value hS = 0 ↔ ∃ a : C S.X₁.1 U 0, d S.X₁.1 U 0 a = z := by
  constructor
  · intro hr
    obtain ⟨s, hs⟩ := Sheaf.H.longSequence_equiv₀_exact₃ hS
      (isTerminalTop (α := Opens T)) r.quotientSection hr
    have ht : ∀ σ, S.g.hom.app (op (inter U σ))
        ((r.primitive - globalCochain S.X₂.1 U s) σ) = 0 := by
      intro σ
      change (map U S.g.hom 0 (r.primitive - globalCochain S.X₂.1 U s)) σ = 0
      rw [map_sub, map_globalCochain, hs, r.quotient, sub_self, Pi.zero_apply]
    choose a ha using fun σ => TopCat.Sheaf.sections_exact_of_left_exact
      hS.exact hS.mono_f _ (ht σ)
    have ha' : map U S.f.hom 0 a = r.primitive - globalCochain S.X₂.1 U s :=
      funext ha
    refine ⟨a, map_f_injective hS 1 ?_⟩
    rw [← d_map, ha', map_sub, d_globalCochain, sub_zero, r.primitive_d]
  · rintro ⟨a, ha⟩
    have ht : d S.X₂.1 U 0 (r.primitive - map U S.f.hom 0 a) = 0 := by
      rw [map_sub, d_map, ha, r.primitive_d, sub_self]
    obtain ⟨s, hs⟩ := exists_globalCochain_eq U S.X₂ hcov _ ht
    have hq : S.g.hom.app (op ⊤) s = r.quotientSection := by
      apply globalCochain_injective U S.X₃ hcov
      rw [← map_globalCochain, hs, map_sub, map_g_f, sub_zero, r.quotient]
    dsimp [Representative.value]
    rw [← hq]
    exact connecting_section_eq_zero_of_lift hS s

/-- Subtracting representatives represents subtraction of one-cochains. -/
def Representative.sub {z z' : C S.X₁.1 U 1}
    (r : Representative (S := S) z) (r' : Representative (S := S) z') :
    Representative (S := S) (z - z') where
  primitive := r.primitive - r'.primitive
  quotientSection := r.quotientSection - r'.quotientSection
  primitive_d := by rw [map_sub, r.primitive_d, r'.primitive_d, map_sub]
  quotient := by rw [map_sub, r.quotient, r'.quotient, map_sub]

/-- Adding representatives represents addition of one-cochains. -/
def Representative.add {z z' : C S.X₁.1 U 1}
    (r : Representative (S := S) z) (r' : Representative (S := S) z') :
    Representative (S := S) (z + z') where
  primitive := r.primitive + r'.primitive
  quotientSection := r.quotientSection + r'.quotientSection
  primitive_d := by rw [map_add, r.primitive_d, r'.primitive_d, map_add]
  quotient := by rw [map_add, r.quotient, r'.quotient, map_add]

set_option backward.isDefEq.respectTransparency false in
lemma Representative.sub_value (hS : S.ShortExact) {z z' : C S.X₁.1 U 1}
    (r : Representative (S := S) z) (r' : Representative (S := S) z') :
    (r.sub r').value hS = r.value hS - r'.value hS := by
  simp only [Representative.value, Representative.sub, map_sub]

set_option backward.isDefEq.respectTransparency false in
lemma Representative.add_value (hS : S.ShortExact) {z z' : C S.X₁.1 U 1}
    (r : Representative (S := S) z) (r' : Representative (S := S) z') :
    (r.add r').value hS = r.value hS + r'.value hS := by
  simp only [Representative.value, Representative.add, map_add]

set_option backward.isDefEq.respectTransparency false in
/-- The connecting class is independent of the chosen representative. -/
theorem Representative.value_eq (hS : S.ShortExact) (hcov : ⊤ ≤ iSup U)
    {z : C S.X₁.1 U 1} (r r' : Representative (S := S) z) :
    r.value hS = r'.value hS := by
  apply sub_eq_zero.1
  rw [← Representative.sub_value]
  apply ((r.sub r').value_eq_zero_iff hS hcov).2
  exact ⟨0, by rw [map_zero, sub_self]⟩

end Representatives

section Quotient

variable {T : TopCat.{u}} (P : TopCat.Presheaf AddCommGrpCat.{u} T)
  {ι : Type w} (U : ι → Opens T)

/-- The subgroup of ordered Čech one-cocycles. -/
def cocycles : AddSubgroup (C P U 1) := (d P U 1).ker

/-- The differential from zero-cochains, with codomain the one-cocycles. -/
def coboundaryHom : C P U 0 →+ cocycles P U where
  toFun a := ⟨d P U 0 a, d_d P U 0 a⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- Ordered Čech degree-one cohomology for this fixed family of opens. -/
abbrev CechH1 := cocycles P U ⧸ (coboundaryHom P U).range

variable {P U}
  {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)}
  [Finite ι] [TopCat.Presheaf.IsFlasque S.X₂.1]

/-- Choose a primitive and quotient section for each one-cocycle. -/
def chosenRepresentative (hcov : ⊤ ≤ iSup U) (z : cocycles S.X₁.1 U) :
    Representative (S := S) z.1 :=
  Classical.choice (exists_representative hcov z.1 z.2)

set_option backward.isDefEq.respectTransparency false in
/-- The additive connecting-class map on Čech one-cocycles. -/
def cocycleClassHom (hS : S.ShortExact) (hcov : ⊤ ≤ iSup U) :
    cocycles S.X₁.1 U →+ Sheaf.H.{u} S.X₁ 1 where
  toFun z := (chosenRepresentative hcov z).value hS
  map_zero' := by
    apply ((chosenRepresentative hcov 0).value_eq_zero_iff hS hcov).2
    exact ⟨0, map_zero _⟩
  map_add' z z' := by
    exact (Representative.value_eq hS hcov (chosenRepresentative hcov (z + z'))
      ((chosenRepresentative hcov z).add (chosenRepresentative hcov z'))).trans
        (Representative.add_value hS _ _)

set_option backward.isDefEq.respectTransparency false in
lemma cocycleClassHom_eq_value (hS : S.ShortExact) (hcov : ⊤ ≤ iSup U)
    (z : cocycles S.X₁.1 U) (r : Representative (S := S) z.1) :
    cocycleClassHom hS hcov z = r.value hS :=
  Representative.value_eq hS hcov _ _

set_option backward.isDefEq.respectTransparency false in
lemma cocycleClassHom_eq_zero_iff (hS : S.ShortExact) (hcov : ⊤ ≤ iSup U)
    (z : cocycles S.X₁.1 U) :
    cocycleClassHom hS hcov z = 0 ↔
      ∃ a : C S.X₁.1 U 0, d S.X₁.1 U 0 a = z.1 :=
  (chosenRepresentative hcov z).value_eq_zero_iff hS hcov

set_option backward.isDefEq.respectTransparency false in
lemma coboundary_range_eq_ker (hS : S.ShortExact) (hcov : ⊤ ≤ iSup U) :
    (coboundaryHom S.X₁.1 U).range = (cocycleClassHom hS hcov).ker := by
  ext z
  change (∃ a, coboundaryHom S.X₁.1 U a = z) ↔ cocycleClassHom hS hcov z = 0
  rw [cocycleClassHom_eq_zero_iff]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

set_option backward.isDefEq.respectTransparency false in
/-- The comparison from a finite full cover, using a short exact sequence with flasque
middle term, to actual first sheaf cohomology. -/
def quotientClassHom (hS : S.ShortExact) (hcov : ⊤ ≤ iSup U) :
    CechH1 S.X₁.1 U →+ Sheaf.H.{u} S.X₁ 1 :=
  QuotientAddGroup.lift _ (cocycleClassHom hS hcov) (coboundary_range_eq_ker hS hcov).le

set_option backward.isDefEq.respectTransparency false in
lemma quotientClassHom_mk (hS : S.ShortExact) (hcov : ⊤ ≤ iSup U)
    (z : cocycles S.X₁.1 U) :
    quotientClassHom hS hcov (QuotientAddGroup.mk z) = cocycleClassHom hS hcov z :=
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem quotientClassHom_injective (hS : S.ShortExact) (hcov : ⊤ ≤ iSup U) :
    Function.Injective (quotientClassHom hS hcov) :=
  (QuotientAddGroup.injective_lift_iff _ _ _).2 (coboundary_range_eq_ker hS hcov)

end Quotient

section Comparison

variable {T : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} T)
  {ι : Type w} [Finite ι] (U : ι → Opens T)

set_option backward.isDefEq.respectTransparency false in
/-- The finite-cover Čech-to-actual-H¹ homomorphism, using the chosen injective embedding. -/
def comparisonHom (hcov : ⊤ ≤ iSup U) :
    CechH1 F.1 U →+ Sheaf.H.{u} F 1 := by
  let S := AbelianSheafFlasque.injectiveSc F
  letI : TopCat.Sheaf.IsFlasque S.X₂ :=
    AbelianSheafFlasque.isFlasque_of_injective (Injective.under F)
  exact quotientClassHom (AbelianSheafFlasque.injectiveSc_shortExact F) hcov

set_option backward.isDefEq.respectTransparency false in
/-- Čech degree-one cohomology on a finite full cover embeds into actual sheaf H¹. -/
theorem comparisonHom_injective (hcov : ⊤ ≤ iSup U) :
    Function.Injective (comparisonHom F U hcov) := by
  let S := AbelianSheafFlasque.injectiveSc F
  let : TopCat.Sheaf.IsFlasque S.X₂ :=
    AbelianSheafFlasque.isFlasque_of_injective (Injective.under F)
  exact quotientClassHom_injective (AbelianSheafFlasque.injectiveSc_shortExact F) hcov

set_option backward.isDefEq.respectTransparency false in
/-- Compute the comparison with any primitive and glued quotient section. -/
theorem comparisonHom_eq_value (hcov : ⊤ ≤ iSup U) (z : cocycles F.1 U)
    (r : Representative (S := AbelianSheafFlasque.injectiveSc F) z.1) :
    comparisonHom F U hcov (QuotientAddGroup.mk z) =
      r.value (AbelianSheafFlasque.injectiveSc_shortExact F) := by
  let S := AbelianSheafFlasque.injectiveSc F
  let : TopCat.Sheaf.IsFlasque S.X₂ :=
    AbelianSheafFlasque.isFlasque_of_injective (Injective.under F)
  exact cocycleClassHom_eq_value (AbelianSheafFlasque.injectiveSc_shortExact F) hcov z r

end Comparison

end Langlands.Cohomology.AbelianSheafCechH1
